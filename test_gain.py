import unittest
from pathlib import Path
import tell
from tell_advanced import explain_gain


class GainTests(unittest.TestCase):
    def test_minimal_and_limited(self):
        base = tell.input_snapshot(str(Path(__file__).with_name("gain.tell")))
        def run(budget):
            return explain_gain(tell, base, "ready", ["power","signal","override"], 3, budget)
        result = run(20)
        self.assertEqual([r["additions"] for r in result["minimal_sufficient_sets"]],
                         [["override"], ["power","signal"]])
        self.assertTrue(result["complete_within_width"])
        self.assertFalse(run(1)["complete_within_width"])
