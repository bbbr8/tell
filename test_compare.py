import copy
from pathlib import Path
import tempfile
import unittest
from tell_compare import compare_models


class ModelComparison(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.root=Path(self.tmp.name)
        (self.root/'good.tell').write_text('tier order: derived > synthetic.\nfact power tier synthetic.\nrule r: ready :- power, signal.\n')
        (self.root/'bad.tell').write_text('tier order: derived > synthetic.\nfact power tier synthetic.\nrule r: ready :- power.\n')
        self.packet={'candidates':[{'id':'good','path':'good.tell'},{'id':'bad','path':'bad.tell'}],
                     'queries':[{'id':'q','goal':'ready','expected':'ABSENT'},{'id':'control','goal':'power','expected':'HOLD'}]}

    def test_counterexample_and_exact_distinguishing_query(self):
        old=copy.deepcopy(self.packet);r=compare_models(self.packet,self.root)
        self.assertEqual(r['accepted'],['good']);self.assertEqual(r['state'],'FINITE_DISAGREEMENT')
        self.assertEqual(r['next_query']['id'],'q');self.assertEqual(self.packet,old)
        self.assertEqual(r['candidates'][1]['counterexamples'][0]['actual'],'HOLD')

    def test_duplicate_programs_form_one_class(self):
        self.packet['candidates']=[self.packet['candidates'][0],{'id':'copy','path':'good.tell'}]
        r=compare_models(self.packet,self.root);self.assertEqual(len(r['classes']),1)
        self.assertEqual(r['state'],'FINITE_AGREEMENT')

    def test_ground_queries_required_and_invalid_models_partial(self):
        self.packet['queries'][0]['goal']='ready(X)'
        self.assertEqual(compare_models(self.packet,self.root)['state'],'PARTIAL')

    def test_no_expected_answer_never_selects_by_agreement(self):
        for q in self.packet['queries']:q.pop('expected')
        r=compare_models(self.packet,self.root);self.assertEqual(r['accepted'],[])
        self.assertFalse(r['expected_statuses_supplied'])

    def test_path_boundary(self):
        self.packet['candidates'][0]['path']='../outside'
        with self.assertRaises(ValueError):compare_models(self.packet,self.root)

    def test_follow_up_conditions_on_known_answers_and_collapses_copies(self):
        (self.root / 'third.tell').write_text('fact power tier synthetic.\nfact spare tier synthetic.\n')
        self.packet['candidates'] += [{'id': 'third', 'path': 'third.tell'},
                                      {'id': 'duplicate', 'path': 'third.tell'}]
        self.packet['queries'].append({'id': 'spare', 'goal': 'spare'})
        result = compare_models(self.packet, self.root)
        follow = result['status_follow_up']
        self.assertEqual(follow['query']['id'], 'spare')
        self.assertEqual(follow['eligible_status_classes'], 2)
        self.assertEqual(follow['largest_remaining_class_count'], 1)
        self.assertEqual(follow['branches']['HOLD']['candidates'], ['duplicate', 'third'])
        self.assertEqual(follow['branches']['ABSENT']['candidates'], ['good'])

    def test_follow_up_distinguishes_conflict_from_agreement(self):
        self.assertEqual(compare_models(self.packet, self.root)['status_follow_up']['state'],
                         'NO_STATUS_DISAGREEMENT')
        self.packet['queries'][1]['expected'] = 'ABSENT'
        self.assertEqual(compare_models(self.packet, self.root)['status_follow_up']['state'],
                         'NO_MATCHING_MODEL')
        self.packet['candidates'] = [{'id': 'gone', 'path': 'missing.tell'}]
        self.assertEqual(compare_models(self.packet, self.root)['status_follow_up']['state'],
                         'NO_COMPLETE_MODEL')

class ExpectedRemainingTests(unittest.TestCase):
    def test_expected_size_and_minimax_can_select_different_queries(self):
        from tell_compare import status_follow_up
        # The two three-way splits have sizes (4,3,1) and (4,2,2).
        rows = []
        for i, (first, second) in enumerate(zip('AAAABBBC', 'AAAABBCC')):
            signature = [first, second] + [str(i == j) for j in range(8)]
            rows.append(dict(id=str(i), complete=True, matches_expectations=True,
                             observations=[dict(state=value) for value in signature]))
        queries = [dict(id=i) for i in range(10)]
        default = status_follow_up(rows, queries)
        self.assertEqual(default['query']['id'], 0)
        self.assertEqual(default['expected_remaining_classes_fraction'], '13/4')
        rows.append({**rows[0], 'id': 'copy'})
        alternate = status_follow_up(rows, queries, 'expected_remaining')
        self.assertEqual(alternate['query']['id'], 1)
        self.assertEqual(alternate['expected_remaining_classes_fraction'], '3')
        self.assertEqual(alternate['largest_remaining_class_count'], 4)
        with self.assertRaises(ValueError):
            status_follow_up(rows, queries, 'unknown')
