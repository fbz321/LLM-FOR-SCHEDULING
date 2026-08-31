#!/usr/bin/env python3

import unittest
from fractions import Fraction

import incremental_verify as verifier
import m5_certify_grid as grid


class CertifyGridTests(unittest.TestCase):
    def test_direct_exact_scheduler_escape(self):
        jobs = (1, 1)
        cache = {
            verifier.prefix_key(2, jobs[:1]): 1,
            verifier.prefix_key(2, jobs[:2]): 1,
        }
        analysis = {"candidates": [{
            "candidate_id": "x",
            "multipliers": ["1/1"],
            "jobs": ["1", "1"],
        }]}
        result = grid.certify_candidates(
            analysis, cache, {}, 2, Fraction(3, 2),
        )
        self.assertEqual(result["complete_candidates"], 1)
        self.assertEqual(result["direct_scheduler_escapes"], 1)
        self.assertEqual(result["threshold_game_escapes"], 0)
        self.assertEqual(result["pass_count"], 0)

    def test_full_game_is_used_when_direct_path_is_not_an_escape(self):
        jobs = (1, 1, 2)
        values = {1: 1, 2: 1, 3: 2}
        cache = {
            verifier.prefix_key(2, jobs[:length]): value
            for length, value in values.items()
        }
        analysis = {"candidates": [{
            "candidate_id": "x",
            "multipliers": ["1/1"],
            "jobs": [str(job) for job in jobs],
        }]}
        result = grid.certify_candidates(
            analysis, cache, {}, 2, Fraction(3, 2),
        )
        self.assertEqual(result["direct_scheduler_escapes"], 0)
        self.assertEqual(result["pass_count"], 1)
        self.assertEqual(
            result["candidates"][0]["certificate"],
            "exact threshold-game PASS",
        )

    def test_missing_prefix_is_reported(self):
        analysis = {"candidates": [{
            "candidate_id": "x",
            "jobs": ["1"],
        }]}
        result = grid.certify_candidates(
            analysis, {}, {}, 2, Fraction(3, 2),
        )
        self.assertEqual(result["complete_candidates"], 0)
        self.assertEqual(result["candidates"][0]["missing"][0]["length"], 1)


if __name__ == "__main__":
    unittest.main()
