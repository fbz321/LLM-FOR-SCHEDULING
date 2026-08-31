#!/usr/bin/env python3

import unittest

import m5_type2_split_probe as split
import rudin_generator


class Type2SplitProbeTests(unittest.TestCase):
    def test_split_is_exact_and_changes_one_job(self):
        base = rudin_generator.published_jobs()
        jobs = split.split_candidate(base, 0, 2, 999)
        changed = split.TYPE2_B_STARTS[0] + 2
        for index, job in enumerate(base):
            multiplier = 999 if index == changed else 1000
            self.assertEqual(jobs[index], job * multiplier)

    def test_invalid_parameters_are_rejected(self):
        base = rudin_generator.published_jobs()
        with self.assertRaisesRegex(ValueError, "stage"):
            split.split_candidate(base, 5, 0, 999)
        with self.assertRaisesRegex(ValueError, "position"):
            split.split_candidate(base, 0, 5, 999)
        with self.assertRaisesRegex(ValueError, "multiplier"):
            split.split_candidate(base, 0, 0, 1000)

    def test_small_grid_has_certified_escapes(self):
        payload = split.enumerate_candidates(
            rudin_generator.published_jobs(), numerators=(999, 1001),
        )
        self.assertEqual(payload["candidate_count"], 50)
        self.assertEqual(payload["escaped"], 50)
        self.assertEqual(payload["survivor_count"], 0)


if __name__ == "__main__":
    unittest.main()
