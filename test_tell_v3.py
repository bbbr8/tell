"""Portable synthetic regression coverage for TELL v3; no case corpus required."""
import contextlib
import hashlib
import io
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from fractions import Fraction

import tell

HEADER = 'tier order: F0 > F1 > native > derived > synthetic.\nanchor A "synthetic fixture".\n'


class TellV3(unittest.TestCase):
    def program(self, text):
        p = tell.parse(HEADER + text)
        tell.fixpoint(p)
        return p

    def reject(self, text, code=2):
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as ex:
            self.program(text)
        self.assertEqual(ex.exception.code, code)

    def cli(self, *args):
        return subprocess.run([sys.executable, str(Path(tell.__file__).resolve()), *args], text=True, capture_output=True, timeout=10)


    def test_expression_precedence_and_exact_decimal(self):
        p = self.program('rule calc: result(X) :- X = (0.1 + 0.2) * 10 - 4 / 2.\n')
        self.assertIn(('result', (Fraction(1),)), p.facts)

    def test_expression_both_sides_of_guard(self):
        p = self.program('rule ok: accepted :- (1 + 2) * 3 == 10 - 1.\n')
        self.assertIn(('accepted', ()), p.facts)

    def test_left_associativity_and_unary(self):
        p = self.program('rule calc: result(X) :- X = -(-3) + 12 / 3 / 2 - 5 - 1.\n')
        self.assertIn(('result', (Fraction(-1),)), p.facts)

    def test_no_space_operators_and_scientific(self):
        p = self.program('rule calc: result(X) :- X=1e-3+2*(3-1).\n')
        self.assertIn(('result', (Fraction('4.001'),)), p.facts)

    def test_exact_rational_literal_roundtrip(self):
        atom = tell.parse_atom('portion(1/3)')
        self.assertEqual(tell.parse_atom(tell.fmt_atom(atom)), atom)

    def test_multiline_rule_and_multiple_statements(self):
        p = self.program('fact value(3) @A tier F0. fact other(4) @A tier F0.\nrule calc:\n result(X) :-\n value(V), % comment\n other(O),\n X = V + O. show result(X).\n')
        self.assertIn(('result', (Fraction(7),)), p.facts)

    def test_quoted_text_punctuation_and_escape(self):
        text = 'Email@A, 50% of \\"Project\\". (phase 1)'.replace('\\"', '"')
        token = json.dumps(text)
        p = self.program('fact label(' + token + ') @A tier F0.\nrule copy: copied(X) :- label(X).\n')
        key = next(k for k in p.facts if k[0] == 'copied')
        self.assertEqual(key[1], (text,))
        self.assertEqual(tell.parse_atom(tell.fmt_atom(key)), key)

    def test_quoted_uppercase_is_constant(self):
        p = self.program('fact label("X") @A tier F0.\nrule copy: copied(V) :- label(V), V == "X".\n')
        self.assertIn(('copied', ('X',)), p.facts)

    def test_loading_another_program_preserves_variable_identity(self):
        p = tell.parse('tier order: X > derived > synthetic.\nanchor A "fixture".\nfact value(X) @A tier X.\nrule copy: copied(V) :- value(V).\n')
        self.program('fact value(3) @A tier F0.\n')
        tell.fixpoint(p)
        self.assertIn(('copied', ('X',)), p.facts)

    def test_dates_and_whole_day_offsets(self):
        p = self.program('fact start(2020-02-28) @A tier F0.\nrule day: next(D, N) :- start(S), D = S + (1 + 1), N = D - S.\n')
        self.assertIn(('next', (tell.Date('2020-03-01'), Fraction(2))), p.facts)

    def test_invalid_date_dimensions(self):
        for expression in ['2020-02-28 * 2', '2020-02-28 + 0.5', '2020-02-28 + 2020-03-01']:
            with self.subTest(expression=expression): self.reject('rule bad: x(X) :- X = ' + expression + '.\n')

    def test_division_by_zero_inside_expression(self):
        self.reject('rule bad: x(X) :- X = 1 / (2 - 2).\n')

    def test_unbound_head_guard_bind_and_negation(self):
        for text in ['rule bad: x(X) :- 1 == 1.', 'rule bad: x :- X > 1.', 'rule bad: x(V) :- V = M + 1.', 'rule bad: x(X) :- not missing(X).']:
            with self.subTest(text=text): self.reject(text)

    def test_aggregate_local_variable_and_bound_group(self):
        p = self.program('fact group(a) @A tier F0.\nfact value(a, 0.1) @A tier F0.\nfact value(a, 0.2) @A tier F0.\nrule total: total(G, S) :- group(G), S = sum(value(G, V), V).\n')
        self.assertIn(('total', ('a', Fraction('0.3'))), p.facts)

    def test_invalid_aggregate_over_variable(self):
        self.reject('rule bad: total(S) :- S = sum(value(V), Missing).\n')

    def test_duplicate_facts_keep_best_and_all_supports(self):
        facts = ['fact present @A tier F0.', 'fact present @A tier derived.', 'open fact present @A tier synthetic.']
        for ordered in itertools.permutations(facts):
            p = self.program('\n'.join(ordered)); rec = p.facts[('present', ())]
            self.assertEqual((rec['truth'], rec['tier']), (tell.TRUE, 'F0'))
            self.assertEqual(len(rec['fact_supports']), 3)

    def test_duplicate_weaker_support_still_visible_to_gate(self):
        p = self.program('fact present @A tier F0.\nfact present @A tier derived.\nforbid weak: atom_tier(present, derived).\n')
        self.assertEqual([h[0] for h in tell.check_forbids(p)], ['weak'])

    def test_duplicate_anchor_and_rule_names_rejected(self):
        self.reject('anchor A "different".\n')
        self.reject('rule r: a :- 1 == 1.\nrule r: b :- 2 == 2.\n')

    def test_cycle_include_is_diagnostic(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)/'loop.tell'; p.write_text('include "loop.tell".\n')
            r = self.cli('run', str(p))
            self.assertEqual(r.returncode, 2); self.assertIn('include cycle', r.stderr); self.assertNotIn('Traceback', r.stderr)

    def test_query_variables_and_exact_values(self):
        p = self.program('fact part(a, 1/3) @A tier F0.\nfact part(b, 0.3) @A tier F1.\n')
        data = tell.query_json(p, tell.parse_atom('part(Name, Value)'))
        self.assertEqual(data['count'], 2)
        self.assertEqual(data['matches'][0]['bindings'], {'Name': 'a', 'Value': '1/3'})

    def test_query_missing_premise_and_failed_guard(self):
        p = self.program('fact account(a, 20) @A tier F0.\nrule r: ready(X) :- account(X, B), receipt(X).\nrule paid: settled(X) :- account(X, B), B <= 0.\n')
        a = tell.query_json(p, tell.parse_atom('ready(a)'))
        b = tell.query_json(p, tell.parse_atom('settled(a)'))
        self.assertEqual(a['state'], 'UNRESOLVED'); self.assertEqual(a['missing_routes'][0]['state'], 'MISSING_PREMISE')
        self.assertEqual(a['missing_routes'][0]['item'], 'receipt(a)')
        self.assertEqual(b['missing_routes'][0]['state'], 'GUARD_FAILED')

    def test_query_open_and_defeated_statuses(self):
        p = self.program('open fact pending @A tier derived.\nfact yes @A tier F0.\nfact no @A tier F0.\ndefeat d for yes :- no.\n')
        tell.apply_defeaters(p)
        self.assertEqual(tell.query_json(p, tell.parse_atom('pending'))['matches'][0]['status'], 'HOLD_WITH_OPEN')
        row = tell.query_json(p, tell.parse_atom('yes'))['matches'][0]
        self.assertEqual(row['status'], 'DEFEATED'); self.assertIn('DEFEATED by d', '\n'.join(row['why']))

    def test_query_limit_and_arity(self):
        p = self.program('fact one(a) @A tier F0.\nfact one(b) @A tier F0.\n')
        self.assertTrue(tell.query_json(p, tell.parse_atom('one(X)'), 1)['truncated'])
        self.assertEqual(tell.query_json(p, tell.parse_atom('one(a, b)'))['count'], 0)

    def test_query_cli_json_and_forbid_withholding(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)/'main.tell'; p.write_text(HEADER + 'fact yes @A tier F0.\n')
            r = self.cli('query', str(p), 'yes', '--json')
            self.assertEqual(r.returncode, 0, r.stderr); self.assertEqual(json.loads(r.stdout)['matches'][0]['atom'], 'yes')
            p.write_text(p.read_text() + 'forbid block: yes.\n')
            r = self.cli('query', str(p), 'yes', '--json')
            self.assertEqual(r.returncode, 3); self.assertEqual(r.stdout, '')

    def test_source_pin_observes_read_bytes_and_strict_refuses(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td); data = root/'data.json'; data.write_text('{"value": 0.1234567890123456789}')
            p = root/'main.tell'; p.write_text(HEADER + 'anchor B "data" file "data.json" sha256 "' + '0'*64 + '".\nfact value(?) from B path "$.value" tier derived.\n')
            prog = tell.load(str(p)); row = tell.source_status(prog)[0]
            self.assertEqual(row['state'], 'PIN_MISMATCH'); self.assertEqual(row['observed_sha256'], hashlib.sha256(data.read_bytes()).hexdigest())
            data.write_text('{"value": 7}')
            self.assertEqual(tell.source_status(prog)[0]['observed_sha256'], row['observed_sha256'])
            r = self.cli('query', str(p), 'value(X)', '--json', '--strict-sources')
            self.assertEqual(r.returncode, 2); self.assertEqual(r.stdout, '')

    def test_external_path_and_json_ambiguities_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td); data = root/'data.json'; p = root/'main.tell'
            for raw, path in [('{"x":1,"x":2}', '$.x'), ('{"x":NaN}', '$.x'), ('{"x":1}', '$.x[bad]')]:
                data.write_text(raw); p.write_text(HEADER + 'anchor B "data" file "data.json".\nfact value(?) from B path "' + path + '" tier derived.\n')
                r = self.cli('run', str(p)); self.assertEqual(r.returncode, 2, r.stderr); self.assertNotIn('Traceback', r.stderr)

    def test_inference_and_binding_limits(self):
        p = tell.parse(HEADER + 'fact n(0) @A tier F0.\nrule more: n(Y) :- n(X), Y = X + 1.\n')
        p.limits['max_rounds'] = 4
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as ex: tell.fixpoint(p)
        self.assertEqual(ex.exception.code, 4)
        p = tell.parse(HEADER + 'fact n(a) @A tier F0.\nfact n(b) @A tier F0.\nrule pairs: pair(X,Y) :- n(X), n(Y).\n')
        p.limits['max_bindings'] = 3
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as ex: tell.fixpoint(p)
        self.assertEqual(ex.exception.code, 4)

    def test_cli_invalid_options_and_limits(self):
        self.assertEqual(self.cli('selftest', '--fake').returncode, 2)
        self.assertEqual(self.cli('query', 'missing.tell', 'x', '--limit', '0').returncode, 2)

    def test_incomplete_syntax_has_diagnostic(self):
        for text in ['fact x(a,) @A tier F0.', 'rule bad: x :- (1 + 2 == 3.', 'fact x("line\nbreak") @A tier F0.', 'fact x @A tier F0']:
            with self.subTest(text=text): self.reject(text)

    def test_date_constant_is_distinct_from_ordinal_number(self):
        date = tell.Date('2020-02-28')
        ordinal = Fraction(date.numerator)
        self.assertNotEqual(date, ordinal)
        self.assertNotEqual(ordinal, date)
        self.assertEqual(len({date, ordinal}), 2)
        p = self.program('fact value(2020-02-28) @A tier F0.\nfact value(' + str(ordinal) + ') @A tier F0.\n')
        self.assertEqual(len([k for k in p.facts if k[0] == 'value']), 2)

    def test_diagnostic_line_after_comments(self):
        src = HEADER + '% a comment\n\nrule bad: result(X) :- 1 == 1.\n'
        error = io.StringIO()
        with contextlib.redirect_stderr(error), self.assertRaises(SystemExit):
            tell.parse(src, 'line-check.tell')
        self.assertIn('line-check.tell:5:', error.getvalue())

    def test_multiline_anchor_pinning_preserves_other_statements(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            data = root / 'data.json'; data.write_text('{"value": 7}')
            p = root / 'main.tell'
            p.write_text(HEADER + 'anchor B\n "multiline" file "data.json". fact kept @A tier F0.\n')
            r = self.cli('verify', str(p), '--pin')
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertIn('fact kept @A tier F0.', p.read_text())
            loaded = tell.load(str(p))
            self.assertIn(('kept', ()), loaded.facts)
            self.assertEqual(loaded.anchors['B']['sha256'], hashlib.sha256(data.read_bytes()).hexdigest())

    def test_reflection_predicates_are_engine_owned(self):
        for src in ['fact atom_tier(x, F0) @A tier F0.',
                    'rule fake: premise_of(x, y) :- 1 == 1.',
                    'rule read: x :- atom_tier(y, F0).']:
            with self.subTest(src=src): self.reject(src)

    def test_reflection_transitive_paths_and_limits(self):
        p = self.program('fact seed @A tier F0.\nrule a: first :- seed.\nrule b: second :- first.\nrule c: last :- second.\nforbid chain: premise_of(last, seed).\n')
        self.assertEqual([h[0] for h in tell.check_forbids(p)], ['chain'])
        p.limits['max_bindings'] = 3
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as ex:
            tell.materialize_meta(p)
        self.assertEqual(ex.exception.code, 4)


if __name__ == '__main__': unittest.main(verbosity=2)
