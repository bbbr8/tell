"""Synthetic boundary tests for exact aggregates and isolated model experiments."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from fractions import Fraction
import tell
import tell_advanced as advanced

HEADER = 'tier order: F0 > F1 > native > derived > synthetic.\nanchor A "synthetic fixture".\n'


class AdvancedLogic(unittest.TestCase):
    def base(self, src):
        return tell.parse(HEADER + src)

    def run_model(self, src):
        p = self.base(src); tell.fixpoint(p); return p

    def reject(self, action, code=2):
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as ex:
            action()
        self.assertEqual(ex.exception.code, code)

    def cli(self, *args):
        return subprocess.run([sys.executable, str(Path(tell.__file__).resolve()), *args], text=True,
                              capture_output=True, timeout=15)

    def test_sum_expression_and_exact_average(self):
        p = self.run_model('fact item(a,0.1,3) @A tier F0. fact item(b,0.2,2) @A tier F0.\n'
                           'rule total: total(S,M) :- S = sum(item(_,P,Q), P * Q), M = avg(item(_,P,Q), P * Q).\n')
        self.assertIn(('total', (Fraction('0.7'), Fraction('0.35'))), p.facts)

    def test_distinct_symbol_counts_and_duplicate_values(self):
        p = self.run_model('fact item(a,blue) @A tier F0. fact item(b,blue) @A tier F0. fact item(c,red) @A tier F0.\n'
                           'rule count: distinct(N) :- N = count_distinct(item(_,C), C).\n')
        self.assertIn(('distinct', (Fraction(2),)), p.facts)

    def test_aggregate_outer_bindings_and_groups(self):
        p = self.run_model('fact group(a,2) @A tier F0. fact group(b,3) @A tier F0.\n'
                           'fact value(a,0.1) @A tier F0. fact value(b,0.2) @A tier F0.\n'
                           'rule total: total(G,S) :- group(G,W), S = sum(value(G,V), V * W).\n')
        self.assertIn(('total', ('a', Fraction('0.2'))), p.facts)
        self.assertIn(('total', ('b', Fraction('0.6'))), p.facts)

    def test_aggregate_empty_semantics(self):
        p = self.run_model('rule zero: zero(S,C) :- S=sum(missing(V),V), C=count_distinct(missing(V),V).\n'
                           'rule empty: average(A) :- A=avg(missing(V),V).\n')
        self.assertIn(('zero', (Fraction(0), Fraction(0))), p.facts)
        self.assertFalse(any(k[0] == 'average' for k in p.facts))

    def test_open_aggregate_and_weakest_tier(self):
        p = self.run_model('fact value(a,1) @A tier F0. open fact value(b,3) @A tier F1.\n'
                           'rule avg: mean(M) :- M=avg(value(_,V),V).\n')
        self.assertEqual((p.facts['mean', (Fraction(2),)]['truth'], p.facts['mean', (Fraction(2),)]['tier']), (tell.OPEN, 'F1'))

    def test_extra_aggregate_argument_rejected(self):
        for expr in ('sum(value(V),V,Missing)', 'count(value(V),V)', 'avg(value(V))'):
            with self.subTest(expr=expr): self.reject(lambda: self.base('rule bad: x(S) :- S='+expr+'.\n'))

    def test_aggregate_unbound_expression_rejected(self):
        self.reject(lambda: self.base('rule bad: x(S) :- S=sum(value(V),V*Missing).\n'))

    def test_numeric_aggregate_date_rejected_distinct_date_allowed(self):
        src='fact day(a,2020-02-28) @A tier F0.\n'
        self.reject(lambda: self.run_model(src+'rule bad: x(S) :- S=avg(day(_,D),D).\n'))
        p=self.run_model(src+'rule ok: x(S) :- S=count_distinct(day(_,D),D).\n')
        self.assertIn(('x',(Fraction(1),)),p.facts)

    def test_plan_positive_recursion_and_strict_dependencies(self):
        p=self.base('fact edge(a,b) @A tier F0.\nrule path: path(X,Y) :- edge(X,Y).\n'
                    'rule walk: path(X,Z) :- path(X,Y),edge(Y,Z).\nrule size: size(N) :- N=count(path(_,_)).\n')
        plan=advanced.dependency_plan(p)
        self.assertTrue(plan['stratified']); self.assertIn(['path'],plan['recursive_components'])
        self.assertGreater(plan['predicate_strata']['size'],plan['predicate_strata']['path'])

    def test_plan_indirect_negative_cycle_has_actual_witness(self):
        p=self.base('rule a: a :- not b. rule b: b :- c. rule c: c :- a.\n')
        plan=advanced.dependency_plan(p); self.assertFalse(plan['stratified'])
        cycle=plan['issues'][0]['cycle']; edges={(x['head'],x['dependency']) for x in plan['dependencies']}
        self.assertEqual(cycle[0],cycle[-1]); self.assertTrue(all(x in edges for x in zip(cycle,cycle[1:])))
        self.reject(lambda: tell.fixpoint(p))

    def test_plan_aggregate_cycle_rejected(self):
        p=self.base('rule r: value(S) :- S=sum(value(V),V).\n')
        self.assertEqual(advanced.dependency_plan(p)['issues'][0]['strict_kind'],'agg')
        self.reject(lambda: tell.fixpoint(p))

    def test_plan_deep_chain_uses_iterative_components(self):
        src='fact p0 @A tier F0.\n'+'\n'.join('rule r%d: p%d :- p%d.'%(i,i,i-1) for i in range(1,1600))
        plan=advanced.dependency_plan(self.base(src)); self.assertTrue(plan['stratified'])
        self.assertEqual(len(plan['components']),1600)

    def test_plan_generative_recursion_is_flagged(self):
        plan=advanced.dependency_plan(self.base('fact n(0) @A tier F0. rule r: n(Y) :- n(X),Y=X+1.\n'))
        self.assertEqual(plan['warnings'][0]['code'],'GENERATIVE_RECURSION')

    def test_reflection_cannot_enter_ordinary_aggregate_rule(self):
        self.reject(lambda: self.base('rule fake: n(N) :- N=count(atom_tier(_,_)).\n'))

    def test_direct_fact_does_not_hide_alternative_rule_gate(self):
        p=self.run_model('fact ready @A tier F0. fact weak @A tier synthetic.\n'
                         'rule alternate: ready :- weak. forbid gate: premise_of(ready,weak).\n')
        self.assertEqual([h[0] for h in tell.check_forbids(p)],['gate'])

    def test_scenario_missing_premise_assumption_is_synthetic(self):
        p=self.base('fact invoice(a) @A tier F0. rule ready: ready(X) :- invoice(X),receipt(X).\n')
        result=advanced.scenario(tell,p,'ready(a)',assumptions=['receipt(a)'])
        self.assertEqual(result['change'],'GAINED')
        self.assertEqual(result['scenario']['matches'][0]['tier'],'synthetic')
        self.assertEqual(result['mode'],'HYPOTHETICAL_MODEL_EXPERIMENT')
        self.assertEqual(p.rounds,0); self.assertNotIn(('receipt',('a',)),p.facts)

    def test_scenario_dates_clone_and_input_withdrawal(self):
        p=self.base('fact day(2020-02-28) @A tier F0. rule next: next(D) :- day(S),D=S+1.\n')
        result=advanced.scenario(tell,p,'next(2020-02-29)',retracts=['day(2020-02-28)'])
        self.assertEqual(result['change'],'LOST'); self.assertIn(('day',(tell.Date('2020-02-28'),)),p.facts)

    def test_scenario_recomputes_aggregates_without_stale_values(self):
        p=self.base('fact value(a,1) @A tier F0. fact value(b,2) @A tier F0. rule total: total(S) :- S=sum(value(_,V),V).\n')
        result=advanced.scenario(tell,p,'total(3)',retracts=['value(b,2)'])
        self.assertEqual(result['change'],'LOST')
        self.assertEqual(advanced.scenario(tell,p,'total(1)',retracts=['value(b,2)'])['change'],'GAINED')

    def test_scenario_closed_negation_recomputed(self):
        p=self.base('fact person(a) @A tier F0. fact blocked(a) @A tier F0.\n'
                    'closed blocked "synthetic list" @A tier F0. rule eligible: eligible(X) :- person(X),not blocked(X).\n')
        result=advanced.scenario(tell,p,'eligible(a)',retracts=['blocked(a)'])
        self.assertEqual(result['change'],'GAINED'); self.assertEqual(result['scenario']['matches'][0]['truth'],'TRUE')

    def test_scenario_external_json_uses_one_read_snapshot(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td); data=root/'data.json'; data.write_text('{"n":3}')
            source=root/'main.tell'; source.write_text(HEADER+'anchor B "data" file "data.json". fact value(?) from B path "$.n" tier F0.\n')
            p=tell.load(str(source)); original=hashlib.sha256(data.read_bytes()).hexdigest(); data.write_text('{"n":99}')
            result=advanced.scenario(tell,p,'value(3)')
            self.assertEqual(result['change'],'UNCHANGED'); self.assertEqual(result['source_status'][0]['observed_sha256'],original)
            self.assertEqual(json.loads(data.read_text())['n'],99)

    def test_scenario_invalid_inputs_and_snapshot_rejected(self):
        p=self.base('fact a @A tier F0. rule b: b :- a.\n')
        for call in (lambda: advanced.scenario(tell,p,'b(X)'),lambda: advanced.scenario(tell,p,'b',retracts=['b']),
                     lambda: advanced.scenario(tell,p,'b',assumptions=['a'],retracts=['a']),
                     lambda: advanced.scenario(tell,p,'b',assumptions=['atom_tier(a,F0)'])):
            self.reject(call)
        tell.fixpoint(p); self.reject(lambda:advanced.scenario(tell,p,'b'))

    def test_scenario_gate_withholds_cli_output(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/'main.tell'; p.write_text(HEADER+'fact a @A tier F0. forbid gate: blocked.\n')
            result=self.cli('scenario',str(p),'a','--assume','blocked','--json')
            self.assertEqual(result.returncode,3); self.assertEqual(result.stdout,'')

    def test_robustness_finds_two_input_minimal_cuts(self):
        p=self.base('fact a @A tier F0. fact b @A tier F0. fact c @A tier F0.\n'
                    'rule both: goal :- a,b. rule alternate: goal :- c.\n')
        result=advanced.robustness(tell,p,'goal',max_remove=2,budget=20)
        self.assertEqual({frozenset(x['removed']) for x in result['minimal_cuts']},{frozenset(('a','c')),frozenset(('b','c'))})
        self.assertTrue(result['coverage']['complete_within_width']); self.assertEqual(result['coverage']['sets_examined'],6)

    def test_robustness_prunes_only_nonminimal_supersets(self):
        p=self.base('fact a @A tier F0. fact b @A tier F0. rule both: goal :- a,b.\n')
        result=advanced.robustness(tell,p,'goal',budget=20)
        self.assertEqual(len(result['minimal_cuts']),2); self.assertEqual(result['coverage']['supersets_pruned'],1)
        self.assertEqual(result['coverage']['variants_evaluated'],2)

    def test_robustness_partial_budget_never_claims_complete(self):
        p=self.base('fact a @A tier F0. fact b @A tier F0. rule both: goal :- a,b.\n')
        result=advanced.robustness(tell,p,'goal',budget=1)
        self.assertFalse(result['coverage']['complete_within_width']); self.assertTrue(result['coverage']['truncated'])
        self.assertEqual(result['coverage']['sets_examined'],1)

    def test_robustness_selected_input_scope_is_explicit(self):
        p=self.base('fact a @A tier F0. fact b @A tier F0. rule both: goal :- a,b.\n')
        result=advanced.robustness(tell,p,'goal',inputs=['a'])
        self.assertEqual(result['coverage']['candidate_input_count'],1); self.assertEqual(result['coverage']['input_universe_count'],2)
        self.assertEqual(result['candidate_inputs'],['a'])

    def test_robustness_duplicate_support_unit_is_whole_atom(self):
        p=self.base('fact a @A tier F0. fact a @A tier F1. rule goal: goal :- a.\n')
        result=advanced.robustness(tell,p,'goal')
        self.assertEqual(result['minimal_cuts'][0]['removed'],['a']); self.assertEqual(len(p.facts['a',()]['fact_supports']),2)

    def test_robustness_gate_failure_separated_from_missing_goal(self):
        p=self.base('fact a @A tier F0. fact b @A tier F0. closed b "synthetic list" @A tier F0.\n'
                    'rule goal: goal :- a. forbid gate: not b.\n')
        result=advanced.robustness(tell,p,'goal')
        gate=next(x for x in result['minimal_cuts'] if x['removed']==['b'])
        self.assertEqual(gate['outcome'],'GATE_BLOCKED'); self.assertEqual(gate['gates'],['gate'])

    def test_robustness_evaluation_errors_leave_minimality_open(self):
        p=self.base('fact n(a) @A tier F0. fact n(b) @A tier F0.\n'
                    'rule goal: goal :- N=count(n(_)),N>0. rule ratio: ratio(R) :- N=count(n(_)),R=1/(N-1).\n')
        result=advanced.robustness(tell,p,'goal',budget=20)
        self.assertEqual(result['minimal_cuts'],[]); self.assertEqual(len(result['uncertain_cuts']),1)
        self.assertEqual(result['coverage']['evaluation_failures'],2); self.assertFalse(result['coverage']['complete_within_width'])

    def test_robustness_nonmonotone_recovery_does_not_invalidate_minimal_cut(self):
        p=self.base('fact a @A tier F0. fact b @A tier F0. fact c @A tier F0.\n'
                    'closed b "synthetic" @A tier F0. closed c "synthetic" @A tier F0.\n'
                    'rule first: goal :- a. rule recovery: goal :- not b,not c.\n')
        result=advanced.robustness(tell,p,'goal',max_remove=3,budget=20)
        self.assertEqual([x['removed'] for x in result['minimal_cuts']],[['a']])
        self.assertEqual(advanced.scenario(tell,p,'goal',retracts=['a','b','c'])['scenario']['matches'][0]['status'],'HOLD')

    def test_robustness_requires_a_supported_ground_baseline(self):
        p=self.base('open fact a @A tier F0.\n')
        self.reject(lambda:advanced.robustness(tell,p,'a'))
        self.reject(lambda:advanced.robustness(tell,p,'a(X)'))
        self.reject(lambda:advanced.robustness(tell,p,'missing'))

    def test_robustness_resource_exhaustion_is_unresolved(self):
        p=self.base('fact n(0) @A tier F0. fact stop @A tier F0. closed stop "synthetic" @A tier F0.\n'
                    'rule grow: n(Y) :- n(X),not stop,Y=X+1.\n')
        p.limits['max_rounds']=4
        result=advanced.robustness(tell,p,'n(0)',budget=20)
        limited=[row for row in result['observations'] if row['result']['state']=='EVALUATION_LIMIT']
        self.assertEqual(len(limited),1); self.assertEqual(limited[0]['removed'],['stop'])
        self.assertFalse(result['coverage']['complete_within_width'])
        self.assertNotIn(['stop'],[row['removed'] for row in result['minimal_cuts']])

    def test_robustness_input_and_budget_limits_are_explicit(self):
        p=self.base('\n'.join('fact p%d @A tier F0.'%i for i in range(129)))
        self.reject(lambda:advanced.robustness(tell,p,'p0'))
        self.reject(lambda:advanced.robustness(tell,p,'p0',budget=10001,inputs=['p0']))
        result=advanced.robustness(tell,p,'p0',inputs=['p0'])
        self.assertEqual(result['coverage']['input_universe_count'],129)
        self.assertTrue(result['coverage']['complete_within_width'])


    def test_analyze_and_robust_cli_json(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/'main.tell'; p.write_text(HEADER+'fact a @A tier F0. rule goal: goal :- a.\n')
            for cmd in (['analyze',str(p),'--json'],['robust',str(p),'goal','--json']):
                result=self.cli(*cmd); self.assertEqual(result.returncode,0,result.stderr); self.assertIn('schema',json.loads(result.stdout))
            p.write_text(HEADER+'rule bad: a :- not a.\n')
            result=self.cli('analyze',str(p),'--json'); self.assertEqual(result.returncode,2)
            self.assertFalse(json.loads(result.stdout)['stratified'])


if __name__ == '__main__': unittest.main(verbosity=2)
