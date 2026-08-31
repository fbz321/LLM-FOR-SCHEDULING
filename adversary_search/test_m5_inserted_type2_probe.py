#!/usr/bin/env python3

import unittest
from fractions import Fraction

import m5_inserted_type2_probe as probe
import rudin_generator


class InsertedType2ProbeTests(unittest.TestCase):
    def test_inserted_copy_is_exact(self):
        base = rudin_generator.published_jobs()
        q = Fraction(7, 5)
        jobs = probe.insert_scaled_type2(base, q)
        self.assertEqual(len(jobs), 81)
        self.assertEqual(jobs[:65], tuple(job * 7 for job in base[:65]))
        self.assertEqual(
            jobs[65:75], tuple(job * 5 for job in base[55:65]),
        )
        self.assertEqual(jobs[75:], tuple(job * 7 for job in base[65:]))

    def test_invalid_scale_is_rejected(self):
        base = rudin_generator.published_jobs()
        with self.assertRaisesRegex(ValueError, "positive"):
            probe.insert_scaled_type2(base, 0)

    def test_small_grid_is_deterministic(self):
        base = rudin_generator.published_jobs()
        q_values = (Fraction(7, 5), Fraction(3, 2))
        first = probe.enumerate_candidates(base, q_values=q_values)
        second = probe.enumerate_candidates(base, q_values=q_values)
        self.assertEqual(first, second)
        self.assertEqual(first["candidate_count"], 2)
        self.assertEqual(
            first["escaped"] + first["survivor_count"], 2,
        )
        self.assertTrue(all(
            candidate["job_count"] == 81
            for candidate in first["candidates"]
        ))


if __name__ == "__main__":
    unittest.main()
