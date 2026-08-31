#!/usr/bin/env python3

import unittest
from fractions import Fraction

import incremental_verify as verifier
import m5_certify_escape_paths as paths


class CertifyEscapePathsTests(unittest.TestCase):
    def test_basic_bound_alone_certifies_escape(self):
        result = paths.certify_path((1, 1), 2, Fraction(3, 2), {})
        self.assertTrue(result["escaped"])
        self.assertEqual(result["bounded_prefixes"], 2)
        self.assertFalse(result["unresolved"])

    def test_exact_opt_settles_prefix_whose_bound_is_too_large(self):
        jobs = (2, 2, 2)
        key = verifier.prefix_key(2, jobs)
        result = paths.certify_path(
            jobs, 2, Fraction(7, 6), {key: 4},
        )
        self.assertTrue(result["escaped"])
        self.assertEqual(result["exact_prefixes"], 1)

    def test_missing_exact_opt_leaves_prefix_unresolved(self):
        jobs = (2, 2, 2)
        result = paths.certify_path(jobs, 2, Fraction(7, 6), {})
        self.assertFalse(result["escaped"])
        self.assertEqual(result["unresolved"][0]["length"], 3)

    def test_bounded_game_finds_non_greedy_escape(self):
        jobs = (1, 4, 4, 2, 1, 4)
        result = paths.bounded_threshold_game(
            jobs, 2, Fraction(6, 5), {},
        )
        self.assertTrue(result["escaped"])
        self.assertGreater(result["states"], len(jobs))
        self.assertEqual(result["bounded_prefixes"], len(jobs))

    def test_bounded_game_pass_is_only_unresolved(self):
        jobs = (1, 1, 2)
        result = paths.bounded_threshold_game(
            jobs, 2, Fraction(3, 2), {},
        )
        self.assertFalse(result["escaped"])

    def test_candidates_fall_back_to_bounded_game(self):
        analysis = {"candidates": [{
            "candidate_id": "x",
            "jobs": ["1", "4", "4", "2", "1", "4"],
        }]}
        payload = paths.certify_candidates(
            analysis, 2, Fraction(6, 5), {},
        )
        self.assertEqual(payload["path_escapes"], 0)
        self.assertEqual(payload["bounded_game_escapes"], 1)
        self.assertEqual(payload["unresolved_count"], 0)


if __name__ == "__main__":
    unittest.main()
