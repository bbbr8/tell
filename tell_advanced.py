"""Inspectable dependency plans and bounded, isolated TELL model experiments.

All experiments operate on a freshly parsed program. Input withdrawal changes a
model snapshot, never its source files. The runtime is passed explicitly so the
CLI and imported API share one set of term and truth semantics.
"""
import collections
import contextlib
import copy
import hashlib
import io
import itertools
import json
import math


def dependency_plan(p):
    nodes = {key[0] for key in p.facts} | set(p.closed)
    edges = []
    arities = collections.defaultdict(set)
    for pred, args in p.facts:
        arities[pred].add(len(args))
    for rule in p.rules:
        head = rule['head'][0]; nodes.add(head)
        arities[head].add(len(rule['head'][1]))
        for kind, payload in rule['body']:
            atom = payload if kind in ('atom', 'not') else payload[2] if kind == 'agg' else None
            if atom is None:
                continue
            nodes.add(atom[0]); arities[atom[0]].add(len(atom[1]))
            edges.append({'head': head, 'dependency': atom[0], 'kind': kind,
                          'strict': kind in ('not', 'agg'), 'rule': rule['name'], 'line': rule['line']})
    graph = {n: set() for n in nodes}; reverse = {n: set() for n in nodes}
    for edge in edges:
        h, d = edge['head'], edge['dependency']
        graph[h].add(d); reverse[d].add(h)
    # Iterative Kosaraju avoids Python recursion limits on long dependency chains.
    seen, finished = set(), []
    for start in sorted(nodes):
        if start in seen:
            continue
        seen.add(start); stack = [(start, iter(sorted(graph[start])))]
        while stack:
            node, adjacent = stack[-1]
            nxt = next(adjacent, None)
            if nxt is None:
                finished.append(node); stack.pop()
            elif nxt not in seen:
                seen.add(nxt); stack.append((nxt, iter(sorted(graph[nxt]))))
    assigned, components = set(), []
    for start in reversed(finished):
        if start in assigned:
            continue
        component, pending = set(), [start]; assigned.add(start)
        while pending:
            node = pending.pop(); component.add(node)
            for nxt in reverse[node]:
                if nxt not in assigned:
                    assigned.add(nxt); pending.append(nxt)
        components.append(sorted(component))
    components.sort()
    owner = {n: i for i, c in enumerate(components) for n in c}
    issues = []
    for edge in edges:
        h, d = edge['head'], edge['dependency']
        if not edge['strict'] or owner[h] != owner[d]:
            continue
        # Produce an actual return path, rather than just naming the component.
        queue = collections.deque([d]); parents = {d: None}
        while queue and h not in parents:
            n = queue.popleft()
            for nxt in sorted(graph[n]):
                if owner[nxt] == owner[h] and nxt not in parents:
                    parents[nxt] = n; queue.append(nxt)
        path, n = [], h
        while n is not None:
            path.append(n); n = parents[n]
        issues.append({'code': 'NON_STRATIFIED_CYCLE', 'rule': edge['rule'],
                       'line': edge['line'], 'strict_kind': edge['kind'],
                       'cycle': [h] + list(reversed(path))})
    levels = {n: 0 for n in nodes}
    if not issues:
        dependencies = {i: set() for i in range(len(components))}
        consumers = {i: set() for i in dependencies}
        weights = {}
        for edge in edges:
            h, d = owner[edge['head']], owner[edge['dependency']]
            if h != d:
                dependencies[h].add(d); consumers[d].add(h)
                weights[h, d] = max(weights.get((h, d), 0), int(edge['strict']))
        remaining = {i: len(ds) for i, ds in dependencies.items()}
        queue = collections.deque(i for i in remaining if remaining[i] == 0)
        component_level = {i: 0 for i in remaining}
        while queue:
            d = queue.popleft()
            for h in sorted(consumers[d]):
                component_level[h] = max(component_level[h], component_level[d] + weights[h, d])
                remaining[h] -= 1
                if remaining[h] == 0:
                    queue.append(h)
        levels = {n: component_level[owner[n]] for n in nodes}
    recursive = [c for c in components if len(c) > 1 or c[0] in graph[c[0]]]
    recursive_preds = {n for c in recursive for n in c}
    warnings = []
    for rule in p.rules:
        if rule['head'][0] in recursive_preds and any(kind == 'bind' and payload[1][0] != 'value'
                                                       for kind, payload in rule['body']):
            warnings.append({'code': 'GENERATIVE_RECURSION', 'rule': rule['name'],
                             'detail': 'Arithmetic in recursive rules may generate new values; inference limits still apply.'})
    grouped = collections.defaultdict(list)
    if not issues:
        for rule in p.rules:
            grouped[levels[rule['head'][0]]].append(rule['name'])
    return {'schema': 'tell_analysis.v1', 'stratified': not issues,
            'predicate_identity': 'name (conservative across arities, matching TELL reflection)',
            'predicate_arities': {n: sorted(v) for n, v in sorted(arities.items())},
            'dependencies': edges, 'components': components, 'recursive_components': recursive,
            'predicate_strata': dict(sorted(levels.items())) if not issues else {},
            'strata': [{'level': level, 'rules': names} for level, names in sorted(grouped.items())],
            'issues': issues, 'warnings': warnings,
            'counts': {'input_atoms': len(p.facts), 'rules': len(p.rules),
                       'forbids': len(p.forbids), 'defeaters': len(p.defeats)},
            'semantics': {'negation': 'closed warrant required for TRUE absence; other absence is OPEN',
                          'aggregates': 'evaluate after their input predicate strata are stable',
                          'defeaters': 'applied after inference; downstream conclusions retain existing semantics'}}


def _ground(r, value):
    atom = r.parse_atom(value) if isinstance(value, str) else value
    if atom is None or any(r.is_var(a) for a in atom[1]):
        r.die('model experiments require ground atoms')
    if atom[0] in r.META_PREDS:
        r.die('reflection predicates are engine owned and cannot be experiment inputs or targets')
    return atom


def _prepare(r, base):
    if base.rounds or any(rec['prov']['kind'] != 'fact' or rec.get('defeated_by') or rec.get('annotated_by')
                          for rec in base.facts.values()):
        r.die('model experiments require a freshly parsed input snapshot, before inference')
    sources = r.source_status(base)
    encoded = {'lines': base.lines, 'facts': [(r.fmt_atom(k), v['truth'], v['tier'],
                                             r.support_rows(base, v))
                                            for k, v in sorted(base.facts.items(), key=lambda x: r.fmt_atom(x[0]))],
               'sources': sources}
    digest = hashlib.sha256(json.dumps(encoded, sort_keys=True, ensure_ascii=False).encode()).hexdigest()
    return sources, digest


def _observation(r, base, goal, removed=(), assumed=(), details=False):
    p = copy.deepcopy(base)
    for key in removed:
        del p.facts[key]
    for key in assumed:
        rec = {'truth': r.TRUE, 'tier': 'synthetic', 'anchors': [], 'used': 0,
               'prov': {'kind': 'fact', 'extern': None, 'line': ('<hypothetical-assumption>', 0)}}
        old = p.facts.get(key)
        supports = (old or {}).get('fact_supports', []) + [dict(rec)]
        if old is None or rec['truth'] > old['truth'] or (rec['truth'] == old['truth'] and p.stronger('synthetic', old['tier'])):
            p.facts[key] = rec
        p.facts[key]['fact_supports'] = supports
    errors = io.StringIO()
    try:
        with contextlib.redirect_stderr(errors):
            r.fixpoint(p)
            hits = r.check_forbids(p)
            if hits:
                return {'state': 'GATE_BLOCKED', 'gates': [h[0] for h in hits],
                        'withheld': True, 'matches': [], 'count': None}
            r.apply_defeaters(p)
            if details:
                data = r.query_json(p, goal)
            else:
                rec = p.facts.get(goal)
                rows = [] if rec is None else [{'atom': r.fmt_atom(goal), 'status': r.status(rec),
                                                'truth': r.TRUTH_NAME[rec['truth']], 'tier': rec['tier']}]
                data = {'state': 'MATCHES' if rows else 'UNRESOLVED', 'matches': rows, 'count': len(rows)}
    except SystemExit as error:
        return {'state': 'EVALUATION_LIMIT' if error.code == 4 else 'EVALUATION_ERROR',
                'exit_code': error.code, 'detail': errors.getvalue().strip(), 'matches': [], 'count': None}
    data.update(gates=[], withheld=False)
    return data


def _known(observation):
    return observation['state'] not in ('EVALUATION_LIMIT', 'EVALUATION_ERROR')


def _holds(observation):
    return observation['state'] != 'GATE_BLOCKED' and any(m['status'] == 'HOLD' and m['truth'] == 'TRUE'
                                                        for m in observation['matches'])


def _compare(before, after):
    if not _known(before) or not _known(after):
        return 'EVALUATION_INCOMPLETE'
    if after['state'] == 'GATE_BLOCKED':
        return 'GATE_BLOCKED'
    if before['state'] == 'GATE_BLOCKED':
        return 'GATE_CLEARED'
    if bool(before['matches']) != bool(after['matches']):
        return 'GAINED' if after['matches'] else 'LOST'
    fields = lambda x: [(m['truth'], m['status'], m['tier']) for m in x['matches']]
    return 'STATUS_OR_TIER_CHANGED' if fields(before) != fields(after) else 'UNCHANGED'


def scenario(r, base, goal, assumptions=(), retracts=()):
    goal = _ground(r, goal)
    assumed = list(dict.fromkeys(_ground(r, a) for a in assumptions))
    removed = list(dict.fromkeys(_ground(r, a) for a in retracts))
    if set(assumed) & set(removed):
        r.die('the same atom cannot be assumed and retracted in one scenario')
    if any(a not in base.facts for a in removed):
        r.die('only an entered input atom can be retracted; derived atoms are recomputed')
    if assumed and 'synthetic' not in base.tiers:
        r.die('hypothetical assumptions require a declared synthetic tier')
    sources, digest = _prepare(r, base)
    before = _observation(r, base, goal, details=True)
    after = _observation(r, base, goal, removed, assumed, details=True)
    for row in (before, after):
        if 'source_status' in row:
            row['source_status'] = sources
    return {'schema': 'tell_scenario.v1', 'runtime_version': r.VERSION,
            'mode': 'HYPOTHETICAL_MODEL_EXPERIMENT', 'snapshot_sha256': digest,
            'query': r.fmt_atom(goal), 'assumptions': [r.fmt_atom(a) for a in assumed],
            'retracted_input_atoms': [r.fmt_atom(a) for a in removed],
            'withdrawal_unit': 'one logical input atom and all its direct supports',
            'baseline': before, 'scenario': after, 'change': _compare(before, after),
            'source_status': sources, 'scope': 'same parsed snapshot, rules, closed warrants and existing defeater semantics; source files unchanged'}


def robustness(r, base, goal, max_remove=2, budget=64, inputs=None):
    if max_remove not in (1, 2, 3) or not isinstance(budget, int) or budget < 1 or budget > 10000:
        r.die('robustness needs max_remove 1..3 and a candidate-set budget 1..10000')
    goal = _ground(r, goal)
    sources, digest = _prepare(r, base)
    baseline = _observation(r, base, goal, details=True)
    if not _known(baseline):
        r.die(baseline['detail'], baseline['exit_code'])
    if baseline['state'] == 'GATE_BLOCKED':
        r.die('baseline forbid gate blocked: ' + ', '.join(baseline['gates']), 3)
    if not _holds(baseline):
        r.die('robustness requires a forbid-clean ground baseline with status HOLD and truth TRUE')
    baseline['source_status'] = sources
    candidates = (list(base.facts) if inputs is None else list(dict.fromkeys(_ground(r, a) for a in inputs)))
    if any(a not in base.facts for a in candidates):
        r.die('robustness candidates must be entered input atoms')
    candidates.sort(key=r.fmt_atom)
    if len(candidates) > 128:
        r.die('more than 128 candidate inputs; use repeated --input arguments to select an explicit scope')
    width = min(max_remove, len(candidates))
    total = sum(math.comb(len(candidates), k) for k in range(1, width + 1))
    minimal, uncertain, observations, results, failed_sets = [], [], [], {}, []
    examined = evaluated = pruned = failures = 0
    choices = itertools.chain.from_iterable(itertools.combinations(candidates, k) for k in range(1, width + 1))
    for choice in itertools.islice(choices, budget):
        examined += 1; key = frozenset(choice)
        if any(cut <= key for cut in failed_sets):
            pruned += 1
            continue
        observation = _observation(r, base, goal, choice)
        evaluated += 1; results[key] = observation
        labels = [r.fmt_atom(a) for a in choice]
        observations.append({'removed': labels, 'change': _compare(baseline, observation), 'result': observation})
        if not _known(observation):
            failures += 1
            continue
        if _holds(observation):
            continue
        failed_sets.append(key)
        # Minimality requires known, successful proper subsets. A failed or
        # resource-limited subset cannot certify a larger set as minimal.
        proper = [frozenset(s) for k in range(1, len(choice)) for s in itertools.combinations(choice, k)]
        unknown = [s for s in proper if s not in results or not _known(results[s])]
        row = {'removed': labels, 'outcome': observation['state'],
               'query_status': observation['matches'][0]['status'] if observation['matches'] else None,
               'gates': observation.get('gates', [])}
        if unknown:
            row['state'] = 'MINIMALITY_UNRESOLVED'; uncertain.append(row)
        else:
            minimal.append((key, row))
    complete = examined == total and failures == 0
    return {'schema': 'tell_robustness.v1', 'runtime_version': r.VERSION,
            'mode': 'HYPOTHETICAL_INPUT_WITHDRAWAL', 'snapshot_sha256': digest,
            'query': r.fmt_atom(goal), 'baseline': baseline,
            'criterion': 'forbid-clean status HOLD with truth TRUE',
            'withdrawal_unit': 'one logical input atom and all its direct supports; rules and closed warrants retained',
            'candidate_inputs': [r.fmt_atom(a) for a in candidates],
            'minimal_cuts': [row for _, row in minimal], 'uncertain_cuts': uncertain,
            'observations': observations, 'source_status': sources,
            'coverage': {'input_universe_count': len(base.facts), 'candidate_input_count': len(candidates),
                         'candidate_scope': 'all entered input atoms' if inputs is None else 'explicit selected input atoms',
                         'max_remove': max_remove, 'candidate_sets_total': total, 'sets_examined': examined,
                         'variants_evaluated': evaluated, 'supersets_pruned': pruned, 'evaluation_failures': failures,
                         'budget': budget, 'complete_within_width': complete, 'truncated': examined < total},
            'scope': 'loaded model sensitivity; input withdrawal does not establish falsity, real-world causation or completeness of external records'}
