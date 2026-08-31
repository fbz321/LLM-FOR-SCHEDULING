#!/usr/bin/env python3

import json
import os
import unittest
from fractions import Fraction

import incremental_verify as verifier
import template_schema

HERE = os.path.dirname(os.path.abspath(__file__))
SEED = os.path.join(HERE, "seeds", "rudin2001_m5.json")
LEGACY_CACHE = os.path.join(
    HERE, "results", "rudin2001", "cache", "m5_prefix_opts.json"
)


@unittest.skipUnless(
    os.path.exists(SEED) and os.path.exists(LEGACY_CACHE),
    "Rudin m=5 seed/cache are not available in this checkout",
)
class RudinBaselineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with open(SEED, encoding="utf-8") as handle:
            template = json.load(handle)
        sizes, metadata = template_schema.materialize(template)
        cls.jobs, scale = verifier.to_int_jobs(sizes)
        cls.m = metadata["m"]
        with open(LEGACY_CACHE, encoding="utf-8") as handle:
            indexed = json.load(handle)
        cls.cache = verifier.empty_cache()
        verifier.import_index_cache(cls.cache, cls.jobs, cls.m, indexed)

    def test_baseline_uses_only_bound_cache_entries(self):
        opt_pref, _, stats = verifier.prepare_prefix_opts(
            self.jobs, self.m, cache=self.cache, allow_compute=False,
        )
        self.assertEqual(len(opt_pref), 72)
        self.assertEqual(stats, {"hits": 71, "misses": 0})

    def test_baseline_reproduces_known_pass(self):
        opt_pref, _, _ = verifier.prepare_prefix_opts(
            self.jobs, self.m, cache=self.cache, allow_compute=False,
        )
        result = verifier.threshold_check(
            self.jobs, self.m, Fraction(874167, 500000), opt_pref,
        )
        self.assertTrue(result["passed"])
        self.assertEqual(result["states"], 6909)
        self.assertEqual(result["violating_states"], 4746)


if __name__ == "__main__":
    unittest.main()
