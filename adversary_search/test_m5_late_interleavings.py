#!/usr/bin/env python3

import itertools
import unittest

import m5_late_interleavings as late
import rudin_generator


class LateInterleavingTests(unittest.TestCase):
    def test_configuration_count_and_uniqueness(self):
        configs = list(late.configurations())
        self.assertEqual(len(configs), 69300)
        self.assertEqual(len(set(configs)), 69300)
        self.assertTrue(all(
            config.count("X") == 4 and config.count("A") == 4 and
            sorted(label for label in config if label not in "XA") ==
            ["f", "s", "t"]
            for config in configs
        ))

    def test_candidates_preserve_late_multiset(self):
        base = rudin_generator.published_jobs()
        values = late.label_values(base)
        for config in itertools.islice(late.configurations(), 10):
            jobs = late.candidate_jobs(base, config, values)
            self.assertEqual(jobs[:late.LATE_START], base[:late.LATE_START])
            self.assertEqual(
                sorted(jobs[late.LATE_START:]),
                sorted(base[late.LATE_START:]),
            )

    def test_manifest_has_small_shared_prefix_space(self):
        base = rudin_generator.published_jobs()
        manifest = late.build_manifest(base, {})
        self.assertEqual(manifest["candidate_count"], 69300)
        self.assertEqual(manifest["required_late_prefixes"], 199)
        self.assertEqual(manifest["missing_prefixes"], 199)


if __name__ == "__main__":
    unittest.main()
