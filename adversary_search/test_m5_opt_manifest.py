#!/usr/bin/env python3

import json
import os
import tempfile
import unittest

import m5_opt_manifest as manifest

HERE = os.path.dirname(os.path.abspath(__file__))
ANALYSIS = os.path.join(
    HERE, "results", "m5_structured", "late_interface_analysis.json"
)
CACHE = os.path.join(
    HERE, "results", "m5_structured", "prefix_opts_content.json"
)


class OptManifestTests(unittest.TestCase):
    def test_manifest_contains_only_mutated_suffixes(self):
        with open(ANALYSIS, encoding="utf-8") as handle:
            records = json.load(handle)["candidates"][:2]
        cached = manifest.load_content_cache(CACHE)
        result = manifest.build_manifest(records, 5, cached)
        self.assertEqual(result["candidate_count"], 2)
        self.assertTrue(result["jobs"])
        self.assertGreaterEqual(min(job["length"] for job in result["jobs"]), 65)
        self.assertLessEqual(max(job["length"] for job in result["jobs"]), 71)
        self.assertEqual(
            len(result["jobs"]),
            len({job["key"] for job in result["jobs"]}),
        )


if __name__ == "__main__":
    unittest.main()
