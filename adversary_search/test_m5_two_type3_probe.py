#!/usr/bin/env python3

import unittest
from fractions import Fraction

import m5_two_type3_probe as probe
import rudin_generator


class TwoType3ProbeTests(unittest.TestCase):
    def test_insertion_is_exact_and_has_expected_order(self):
        base = rudin_generator.published_jobs()
        q = Fraction(1001, 1000)
        jobs = probe.insert_scaled_type3(base, q)
        self.assertEqual(len(jobs), 76)
        self.assertEqual(
            jobs[:probe.TYPE3_START],
            tuple(job * 1001 for job in base[:probe.TYPE3_START]),
        )
        self.assertEqual(
            jobs[probe.TYPE3_START:probe.TYPE3_STOP],
            tuple(job * 1000 for job in base[65:70]),
        )
        self.assertEqual(
            jobs[probe.TYPE3_STOP:],
            tuple(job * 1001 for job in base[65:]),
        )

    def test_invalid_q_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "greater than one"):
            probe.insert_scaled_type3(rudin_generator.published_jobs(), 1)

    def test_candidate_ids_are_deterministic_and_parameter_bound(self):
        self.assertEqual(
            probe.candidate_id(Fraction(1001, 1000)),
            probe.candidate_id(Fraction(1001, 1000)),
        )
        self.assertNotEqual(
            probe.candidate_id(Fraction(1001, 1000)),
            probe.candidate_id(Fraction(1002, 1000)),
        )

    def test_small_grid_has_certified_escape_paths(self):
        payload = probe.enumerate_candidates(
            rudin_generator.published_jobs(),
            q_values=(Fraction(1001, 1000), Fraction(11, 10)),
        )
        self.assertFalse(payload["certifying_construction"])
        self.assertEqual(payload["candidate_count"], 2)
        self.assertEqual(payload["escaped"], 2)
        self.assertEqual(payload["survivor_count"], 0)
        self.assertTrue(all(
            record["escaped"] for record in payload["candidates"]
        ))


if __name__ == "__main__":
    unittest.main()
