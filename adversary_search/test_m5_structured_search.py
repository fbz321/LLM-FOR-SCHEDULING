#!/usr/bin/env python3
"""Tests for the Rudin m=5 singleton-position search neighborhood."""

import json
import os
import unittest

import m5_structured_search as search

HERE = os.path.dirname(os.path.abspath(__file__))
SEED = os.path.join(HERE, "seeds", "rudin2001_m5.json")
RESULT = os.path.join(
    HERE, "results", "m5_structured",
    "singleton_permutations_above_rudin.json",
)


@unittest.skipUnless(os.path.exists(SEED), "Rudin m=5 seed is unavailable")
class StructuredSearchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.template, cls.jobs, cls.m, cls.scale = search.load_seed(SEED)
        cls.blocks = search.mixed_blocks(cls.template)

    def test_baseline_neighborhood_shape(self):
        self.assertEqual(self.m, 5)
        self.assertEqual(len(self.jobs), 71)
        self.assertEqual(len(self.blocks), 6)
        self.assertEqual(
            search.candidate_jobs(
                self.jobs, self.blocks, (4,) * len(self.blocks)
            ),
            self.jobs,
        )

    def test_position_candidates_preserve_complete_multiset(self):
        candidate = search.candidate_jobs(
            self.jobs, self.blocks, (0, 1, 2, 3, 4, 0)
        )
        self.assertEqual(sorted(candidate), sorted(self.jobs))

    def test_required_prefix_set_is_deterministic(self):
        first = search.required_prefixes(self.jobs, self.blocks, self.m)
        second = search.required_prefixes(self.jobs, self.blocks, self.m)
        self.assertEqual(first, second)
        self.assertEqual(len(first), 54)

    @unittest.skipUnless(os.path.exists(RESULT), "search result is unavailable")
    def test_recorded_search_exhausts_neighborhood(self):
        with open(RESULT, encoding="utf-8") as handle:
            result = json.load(handle)
        self.assertEqual(result["tested"], 5 ** 6)
        self.assertEqual(result["pass_count"], 0)
        self.assertGreater(result["tau_decimal"], 1.74833497030641)


if __name__ == "__main__":
    unittest.main()
