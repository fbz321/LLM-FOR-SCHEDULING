#!/usr/bin/env python3

import unittest
from fractions import Fraction

import incremental_verify as verifier
import m5_verify_shortlist as check


class VerifyShortlistTests(unittest.TestCase):
    def test_incomplete_candidate_is_reported(self):
        analysis = {
            "candidates": [{
                "candidate_id": "x",
                "multipliers": ["1/1"],
                "jobs": ["1", "1", "2"],
            }]
        }
        base = {
            verifier.prefix_key(2, (1,)): 1,
            verifier.prefix_key(2, (1, 1)): 1,
        }
        result = check.verify_candidates(
            analysis, base, {}, 2, Fraction(3, 2),
        )
        self.assertEqual(result["complete_candidates"], 0)
        self.assertEqual(result["candidates"][0]["missing"][0]["length"], 3)

    def test_complete_candidate_is_checked_exactly(self):
        jobs = (1, 1, 2)
        values = {1: 1, 2: 1, 3: 2}
        cache = {
            verifier.prefix_key(2, jobs[:length]): value
            for length, value in values.items()
        }
        analysis = {
            "candidates": [{
                "candidate_id": "x",
                "multipliers": ["1/1"],
                "jobs": [str(job) for job in jobs],
            }]
        }
        result = check.verify_candidates(
            analysis, cache, {}, 2, Fraction(3, 2),
        )
        self.assertEqual(result["complete_candidates"], 1)
        self.assertEqual(result["pass_count"], 1)
        self.assertTrue(result["candidates"][0]["passed"])

    def test_escape_path_records_exact_maximum_ratio(self):
        jobs = (1, 1)
        cache = {
            verifier.prefix_key(2, jobs[:1]): 1,
            verifier.prefix_key(2, jobs[:2]): 1,
        }
        analysis = {
            "candidates": [{
                "candidate_id": "x",
                "multipliers": ["1/1"],
                "jobs": [str(job) for job in jobs],
            }]
        }
        result = check.verify_candidates(
            analysis, cache, {}, 2, Fraction(2, 1),
        )
        record = result["candidates"][0]
        self.assertFalse(record["passed"])
        self.assertEqual(record["escape_max_ratio"], "1/1")
        self.assertEqual(record["escape_max_prefix"], 2)


if __name__ == "__main__":
    unittest.main()
