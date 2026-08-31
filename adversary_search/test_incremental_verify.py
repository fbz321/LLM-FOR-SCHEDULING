#!/usr/bin/env python3

import json
import os
import tempfile
import unittest
from fractions import Fraction

import incremental_verify as verifier
from m4_search import opt


class IncrementalVerifierTests(unittest.TestCase):
    def test_cache_reuses_exact_prefix_multisets(self):
        calls = []

        def solver(jobs, m):
            calls.append((jobs, m))
            return opt(jobs, m)

        cache = verifier.empty_cache()
        _, cache, first = verifier.prepare_prefix_opts(
            (2, 1, 3), 2, cache=cache, solver=solver,
        )
        self.assertEqual(first, {"hits": 0, "misses": 3})
        _, _, second = verifier.prepare_prefix_opts(
            (1, 2, 3), 2, cache=cache, solver=solver,
        )
        self.assertEqual(second, {"hits": 2, "misses": 1})
        self.assertEqual(len(calls), 4)

    def test_suffix_mutation_invalidates_only_changed_prefixes(self):
        cache = verifier.empty_cache()
        _, cache, _ = verifier.prepare_prefix_opts((1, 2, 3, 4), 2, cache=cache)
        _, _, stats = verifier.prepare_prefix_opts((1, 2, 5, 4), 2, cache=cache)
        self.assertEqual(stats, {"hits": 2, "misses": 2})

    def test_tampered_cache_entry_is_rejected(self):
        cache = verifier.empty_cache()
        verifier.put_opt(cache, 2, (1,), 1)
        key = verifier.put_opt(cache, 2, (1, 2), 2)
        cache["entries"][key]["jobs"] = ["9"]
        with self.assertRaisesRegex(ValueError, "does not match"):
            verifier.prepare_prefix_opts(
                (1, 2), 2, cache=cache, allow_compute=False,
            )

    def test_cache_round_trip(self):
        cache = verifier.empty_cache()
        verifier.put_opt(cache, 2, (1, 2), 2)
        with tempfile.TemporaryDirectory() as directory:
            path = os.path.join(directory, "prefix.json")
            verifier.save_cache(path, cache)
            self.assertEqual(verifier.load_cache(path), cache)

    def test_serial_solver_matches_bruteforce_cases(self):
        for jobs, m, expected in [
                ((3, 2, 2), 2, 4),
                ((4, 3, 3, 2), 3, 5),
                ((5, 4, 3, 2, 1), 3, 5)]:
            self.assertEqual(opt(jobs, m), expected)

    def test_threshold_pass_and_escape_witness(self):
        jobs = (1, 1, 2)
        opt_pref, cache, _ = verifier.prepare_prefix_opts(
            jobs, 2, cache=verifier.empty_cache(),
        )
        passed = verifier.threshold_check(
            jobs, 2, Fraction(3, 2), opt_pref, include_path=True,
        )
        failed = verifier.threshold_check(
            jobs, 2, Fraction(8, 5), opt_pref, include_path=True,
        )
        self.assertTrue(passed["passed"])
        self.assertFalse(failed["passed"])
        self.assertEqual(len(failed["escape_path"]), len(jobs))

    def test_imported_legacy_cache_is_bound_to_sequence(self):
        cache = verifier.empty_cache()
        verifier.import_index_cache(cache, (1, 2), 2, {"1": "1", "2": "2"})
        _, _, stats = verifier.prepare_prefix_opts(
            (1, 2), 2, cache=cache, allow_compute=False,
        )
        self.assertEqual(stats, {"hits": 2, "misses": 0})
        with self.assertRaises(KeyError):
            verifier.prepare_prefix_opts(
                (2, 1), 2, cache=cache, allow_compute=False,
            )


if __name__ == "__main__":
    unittest.main()
