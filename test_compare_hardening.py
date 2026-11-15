from pathlib import Path
import hashlib
import tempfile
import unittest
from unittest.mock import patch
import tell
from tell_compare import compare_models


class ModelHardening(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        (self.root/'main.tell').write_text('include "part.tell".\n')
        (self.root/'part.tell').write_text('fact ready tier synthetic.\n')
        self.packet={'candidates':[{'id':'p','path':'main.tell'}],
                     'queries':[{'id':'q','goal':'ready','expected':'HOLD'}]}

    def test_dependency_drift_withholds_observations(self):
        original=tell.fixpoint
        def changed(model):
            original(model);(self.root/'part.tell').write_text('fact changed tier synthetic.\n')
        with patch.object(tell,'fixpoint',changed):r=compare_models(self.packet,self.root)
        self.assertEqual(r['state'],'PARTIAL');self.assertEqual(r['accepted'],[])
        self.assertEqual(r['candidates'][0]['error'],'INPUT_CHANGED')
        self.assertEqual(r['candidates'][0]['observations'],[])

    def test_main_drift_is_reported_per_candidate(self):
        original=tell.fixpoint
        def changed(model):
            original(model);(self.root/'main.tell').write_text('fact changed tier synthetic.\n')
        with patch.object(tell,'fixpoint',changed):r=compare_models(self.packet,self.root)
        self.assertEqual(r['candidates'][0]['error'],'INPUT_CHANGED')

    def test_deleted_dependency_is_reported(self):
        original=tell.fixpoint
        def changed(model):original(model);(self.root/'part.tell').unlink()
        with patch.object(tell,'fixpoint',changed):r=compare_models(self.packet,self.root)
        self.assertEqual(r['candidates'][0]['error'],'INPUT_CHANGED')

    def test_stable_dependency_hashes_bound_to_read_bytes(self):
        r=compare_models(self.packet,self.root)
        self.assertEqual(r['accepted'],['p'])
        self.assertTrue(r['candidates'][0]['inputs_unchanged'])
        self.assertEqual(len(r['candidates'][0]['program_files']),2)

    def test_invalid_expected_state_is_value_error(self):
        self.packet['queries'][0]['expected']=[]
        with self.assertRaises(ValueError):compare_models(self.packet,self.root)

    def anchored(self):
        data=self.root/'data.json';data.write_text('{"value":1}')
        sha=hashlib.sha256(data.read_bytes()).hexdigest()
        with (self.root/'main.tell').open('a') as out:
            out.write('anchor B "data" file "data.json" sha256 "'+sha+'".\n')
        return data

    def test_unused_anchor_changed_after_initial_strict_check(self):
        data=self.anchored();original=tell.input_snapshot
        def changed(*args,**kwargs):
            model=original(*args,**kwargs);data.write_text('{"value":2}');return model
        with patch.object(tell,'input_snapshot',changed):r=compare_models(self.packet,self.root)
        self.assertEqual(r['accepted'],[])
        self.assertEqual(r['candidates'][0]['error'],'INPUT_CHANGED')

    def test_unused_anchor_changed_during_evaluation(self):
        data=self.anchored();original=tell.fixpoint
        def changed(model):original(model);data.write_text('{"value":2}')
        with patch.object(tell,'fixpoint',changed):r=compare_models(self.packet,self.root)
        self.assertEqual(r['accepted'],[])
        self.assertEqual(r['candidates'][0]['error'],'INPUT_CHANGED')

    def test_stable_unused_anchor_retains_declared_fingerprint(self):
        data=self.anchored();r=compare_models(self.packet,self.root)
        self.assertEqual(r['accepted'],['p'])
        self.assertEqual(r['candidates'][0]['anchor_files'][str(data.resolve())],hashlib.sha256(data.read_bytes()).hexdigest())


    def test_missing_candidate_preserves_other_results(self):
        self.packet['candidates'].insert(0, {'id': 'missing', 'path': 'missing.tell'})
        result = compare_models(self.packet, self.root)
        self.assertEqual(result['state'], 'PARTIAL')
        self.assertEqual(result['accepted'], ['p'])
        missing = result['candidates'][0]
        self.assertEqual(missing['error'], 'INPUT_UNAVAILABLE')
        self.assertIsNone(missing['program_sha256'])
        self.assertEqual(missing['observations'], [])
