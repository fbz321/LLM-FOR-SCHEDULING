#!/usr/bin/env python3

import os
import unittest
from fractions import Fraction

import m5_late_interface as search

HERE = os.path.dirname(os.path.abspath(__file__))
SEED = os.path.join(HERE, "seeds", "rudin2001_m5.json")


class LateInterfaceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.jobs, cls.m = search.load_jobs(SEED)

    def test_identity_mutation_preserves_baseline(self):
        self.assertEqual(
            search.mutate(self.jobs, (Fraction(1),) * 4),
            self.jobs,
        )

    def test_mutation_changes_only_declared_indices(self):
        candidate = search.mutate(
            self.jobs,
            (Fraction(1001, 1000), Fraction(999, 1000),
             Fraction(1001, 1000), Fraction(999, 1000)),
        )
        changed = {
            index for index, pair in enumerate(zip(self.jobs, candidate))
            if pair[0] != pair[1]
        }
        expected = {index for group in search.MUTABLE_GROUPS for index in group}
        self.assertEqual(changed, expected)

    def test_candidate_ids_are_deterministic(self):
        config = (Fraction(1), Fraction(1001, 1000), Fraction(1), Fraction(1))
        self.assertEqual(search.candidate_id(config), search.candidate_id(config))

    def test_small_grid_count_and_ranking(self):
        grid = (Fraction(999, 1000), Fraction(1), Fraction(1001, 1000))
        result = search.enumerate_candidates(
            self.jobs, self.m, multipliers=grid, retain=5,
        )
        self.assertEqual(result["grid_size"], 3 ** 4 - 1)
        self.assertEqual(result["retained"], 5)
        ratios = [
            Fraction(candidate["optimistic_ratio"])
            for candidate in result["candidates"]
        ]
        self.assertEqual(ratios, sorted(ratios, reverse=True))


if __name__ == "__main__":
    unittest.main()
