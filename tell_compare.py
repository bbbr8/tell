"""Finite, source-pinned comparison of proposed TELL rule models.

Produces executable counterexample feedback from caller-supplied ground queries.
Model generation and the expected statuses are external. Programs remain trusted
local inputs, including any explicitly declared file dependencies.
"""
import argparse
from collections import Counter
import contextlib
import hashlib
from fractions import Fraction
from functools import lru_cache
import io
import json
from pathlib import Path
import tell
from tell_advanced import _ground

STATES={'HOLD','HOLD_WITH_OPEN','DEFEATED','ABSENT','WITHHELD'}


class InputChanged(ValueError):
    pass


def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False)
def digest(value):return hashlib.sha256(encoded(value).encode()).hexdigest()


def optimal_status_depth(signatures):
    """Find the smallest worst-case number of adaptive questions for these classes."""
    rows = list(signatures)
    partitions = {}
    for column in range(len(rows[0])):
        masks = {}
        for i, row in enumerate(rows):
            masks[row[column]] = masks.get(row[column], 0) | (1 << i)
        # Columns inducing the same partition give the same future information.
        partition = tuple(sorted(masks.values()))
        if len(partition) > 1:
            partitions.setdefault(partition, column)

    @lru_cache(maxsize=None)
    def solve(remaining):
        if remaining.bit_count() == 1:
            return 0, None
        best = None
        for masks, column in partitions.items():
            children = [mask & remaining for mask in masks if mask & remaining]
            if len(children) < 2:
                continue
            depth = 1 + max(solve(child)[0] for child in children)
            if best is None or depth < best[0]:
                best = depth, column
                if depth == 1:
                    break
        return best

    return solve((1 << len(rows)) - 1)


def status_follow_up(rows, queries, objective="minimax"):
    """Plan a status question among complete models consistent with supplied answers."""
    if objective not in ("minimax", "expected_remaining", "optimal_depth"):
        raise ValueError("status_objective must be minimax, expected_remaining or optimal_depth")
    pending = [i for i, query in enumerate(queries) if 'expected' not in query]
    signatures = {}
    for row in rows:
        if row['complete'] and row['matches_expectations']:
            signature = tuple(row['observations'][i]['state'] for i in pending)
            signatures.setdefault(signature, []).append(row['id'])
    report = {'eligible_status_classes': len(signatures), 'query': None,
              'incomplete_candidates': sorted(r['id'] for r in rows if not r['complete'])}
    if not signatures:
        report['state'] = 'NO_MATCHING_MODEL' if any(r['complete'] for r in rows) else 'NO_COMPLETE_MODEL'
        return report
    if len(signatures) == 1:
        if objective == "optimal_depth":
            report.update(objective=objective, minimum_worst_case_questions=0)
        return {**report, 'state': 'NO_STATUS_DISAGREEMENT'}

    def partition_score(column):
        counts = Counter(signature[column] for signature in signatures)
        if objective == "expected_remaining":
            return sum(size * size for size in counts.values()), max(counts.values()), column
        return max(counts.values()), -len(counts), column

    if objective == "optimal_depth":
        depth, column = optimal_status_depth(signatures)
        report["minimum_worst_case_questions"] = depth
    else:
        column = min(range(len(pending)), key=partition_score)
    branches = {}
    for signature, names in signatures.items():
        branch = branches.setdefault(signature[column], {'status_classes': 0, 'candidates': []})
        branch['status_classes'] += 1
        branch['candidates'].extend(names)
    for branch in branches.values():
        branch['candidates'].sort()
    sizes = [branch["status_classes"] for branch in branches.values()]
    expected = Fraction(sum(size * size for size in sizes), len(signatures))
    return {**report, "objective": objective, "expected_remaining_classes_fraction": str(expected),
            'state': 'NEEDS_STATUS', 'query': dict(queries[pending[column]]),
            'branches': branches, 'largest_remaining_class_count': max(sizes)}


def compare_models(packet,root=Path('.')):
    if not isinstance(packet,dict):raise ValueError('Comparison packet must be an object')
    candidates=packet.get('candidates');queries=packet.get('queries')
    if not isinstance(candidates,list) or not 1<=len(candidates)<=16:raise ValueError('Supply 1..16 model candidates')
    if not isinstance(queries,list) or not 1<=len(queries)<=64:raise ValueError('Supply 1..64 ground queries')
    seen=set()
    for q in queries:
        if not isinstance(q,dict) or set(q)-{'id','goal','expected'} or not isinstance(q.get('id'),str) or not q['id'] or q['id'] in seen or not isinstance(q.get('goal'),str):raise ValueError('Query IDs must be unique text and goals must be ground text')
        seen.add(q['id'])
        if 'expected' in q and (not isinstance(q['expected'],str) or q['expected'] not in STATES):raise ValueError('Unknown expected query state')
    rows=[];groups={};seen=set()
    for candidate in candidates:
        if not isinstance(candidate,dict) or set(candidate)!={'id','path'} or not isinstance(candidate['id'],str) or not candidate['id'] or candidate['id'] in seen:raise ValueError('Candidates need unique id and relative path')
        seen.add(candidate['id']);path=(Path(root)/candidate['path']).resolve()
        if not path.is_relative_to(Path(root).resolve()):raise ValueError('Candidate path leaves packet directory')
        row = {'id': candidate['id'], 'program_sha256': None, 'complete': False,
               'observations': [], 'counterexamples': []}
        err=io.StringIO()
        try:
            with path.open('rb') as program:
                raw = program.read(1048577)
            if len(raw) > 1048576:
                raise ValueError('Model exceeds 1 MiB')
            row['program_sha256'] = hashlib.sha256(raw).hexdigest()
            with contextlib.redirect_stderr(err):
                model=tell.input_snapshot(str(path),limits={'max_facts':10000,'max_rounds':200,'max_bindings':20000},strict_sources=True)
                files=dict(model.program_file_hashes)
                if files.get(str(path))!=row['program_sha256']:raise InputChanged('Main program changed during load')
                anchors={}
                for a in model.anchors.values():
                    if a.get('file'):
                        p=Path(a['dir'])/a['file'];sha=hashlib.sha256(p.read_bytes()).hexdigest()
                        if sha!=a['sha256']:raise InputChanged('Anchor changed after strict source check')
                        anchors[str(p.resolve())]=sha
                for p,sha in model._read_sources.items():
                    if anchors.get(str(Path(p).resolve()))!=sha:raise InputChanged('Anchor changed during load')
                goals=[_ground(tell,q['goal']) for q in queries]
                tell.fixpoint(model);gates=tell.check_forbids(model)
                if not gates:tell.apply_defeaters(model)
            for p,sha in {**files,**anchors}.items():
                try:unchanged=hashlib.sha256(Path(p).read_bytes()).hexdigest()==sha
                except OSError:unchanged=False
                if not unchanged:raise InputChanged('Input changed while evaluating: '+p)
            for q,goal in zip(queries,goals):
                rec=model.facts.get(goal)
                state='WITHHELD' if gates else tell.status(rec) if rec else 'ABSENT'
                item={'id':q['id'],'goal':tell.fmt_atom(goal),'state':state,
                      'truth':None if gates or rec is None else tell.TRUTH_NAME[rec['truth']],
                      'tier':None if gates or rec is None else rec['tier']}
                row['observations'].append(item)
                if 'expected' in q and state!=q['expected']:
                    row['counterexamples'].append({'query':q['id'],'goal':q['goal'],'expected':q['expected'],'actual':state})
            row.update(complete=True,source_status=tell.source_status(model),program_files=files,
                       anchor_files=anchors,inputs_unchanged=True,matches_expectations=not row['counterexamples'])
            groups.setdefault(digest(row['observations']),{'candidates':[],'observations':row['observations']})['candidates'].append(row['id'])
        except SystemExit as exc:
            row.update(error='EVALUATION_LIMIT' if exc.code==4 else 'INVALID_MODEL',diagnostic=err.getvalue().strip())
        except InputChanged as exc:
            row.update(error='INPUT_CHANGED',diagnostic=str(exc),inputs_unchanged=False)
        except (OSError,UnicodeError) as exc:
            row.update(error='INPUT_UNAVAILABLE',diagnostic=str(exc))
        rows.append(row)
    classes=[{'class_id':key,**value} for key,value in sorted(groups.items())]
    next_query=None
    if len(classes)>1:
        scores=[]
        for i,q in enumerate(queries):
            bins=Counter(encoded(c['observations'][i]) for c in classes)
            if len(bins)>1:scores.append((max(bins.values()),-len(bins),i))
        worst,_,i=min(scores);next_query={**queries[i],'largest_remaining_class_count':worst}
    expected_supplied=any('expected' in q for q in queries)
    return {'schema':'tell.compare.v1','runtime_version':tell.VERSION,'query_sha256':digest(queries),
            'state':'PARTIAL' if any(not r['complete'] for r in rows) else 'FINITE_DISAGREEMENT' if len(classes)>1 else 'FINITE_AGREEMENT',
            'candidates':rows,'classes':classes,'next_query':next_query,
            'status_follow_up':status_follow_up(rows, queries, packet.get("status_objective", "minimax")),
            'accepted':[r['id'] for r in rows if r['complete'] and r['matches_expectations']] if expected_supplied else [],
            'expected_statuses_supplied':expected_supplied,
            'scope':'declared finite ground queries; agreement does not establish program equivalence'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('packet',type=Path);a=p.parse_args()
    try:result=compare_models(json.loads(a.packet.read_text()),a.packet.parent)
    except (ValueError,KeyError,TypeError,OSError) as exc:p.exit(2,str(exc)+'\n')
    print(json.dumps(result,indent=2));return 1 if result['state']=='PARTIAL' else 0


if __name__=='__main__':raise SystemExit(main())
