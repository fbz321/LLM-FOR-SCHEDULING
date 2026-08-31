#!/usr/bin/env python3

import json
import os
import tempfile
import unittest

import incremental_verify as verifier
import run_opt_manifest as runner


class ManifestRunnerTests(unittest.TestCase):
    def manifest(self):
        raw = [
            {"m": 2, "length": 2, "jobs": ["2", "2"]},
            {"m": 2, "length": 3, "jobs": ["3", "2", "1"]},
            {"m": 2, "length": 4, "jobs": ["4", "3", "2", "1"]},
        ]
        for item in raw:
            item["key"] = verifier.prefix_key(
                item["m"], tuple(int(job) for job in item["jobs"])
            )
        return {"jobs": raw}

    def test_select_skips_completed_and_filters_lengths(self):
        manifest = self.manifest()
        completed_key = manifest["jobs"][1]["key"]
        results = {"version": 1, "entries": {completed_key: {"opt": "3"}}}
        selected = runner.select_jobs(
            manifest, results, min_length=2, max_length=3,
        )
        self.assertEqual([item["length"] for item in selected], [2])

    def test_shards_partition_work(self):
        results = {"version": 1, "entries": {}}
        left = runner.select_jobs(self.manifest(), results, 0, 2)
        right = runner.select_jobs(self.manifest(), results, 1, 2)
        all_keys = {item["key"] for item in self.manifest()["jobs"]}
        self.assertEqual(
            {item["key"] for item in left} | {item["key"] for item in right},
            all_keys,
        )
        self.assertFalse(
            {item["key"] for item in left} & {item["key"] for item in right}
        )

    def test_matching_bounds_fast_path(self):
        jobs = (10, 9, 8, 7)
        result = runner.solve_item(
            {"key": verifier.prefix_key(2, jobs), "m": 2, "length": 4,
             "jobs": [str(job) for job in jobs]},
            workers=2,
            split_depth=2,
        )
        self.assertEqual(result["method"], "matching-bounds")
        self.assertEqual(result["opt"], "17")

    def test_manifest_key_mismatch_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "content key mismatch"):
            runner.solve_item(
                {"key": "bad", "m": 2, "length": 2, "jobs": ["2", "2"]},
                workers=1,
                split_depth=1,
            )

    def test_run_is_resumable(self):
        manifest = self.manifest()
        with tempfile.TemporaryDirectory() as directory:
            output = os.path.join(directory, "results.json")
            first, summary = runner.run(
                manifest, output, workers=1, split_depth=2, limit=2,
            )
            self.assertEqual(summary["completed"], 2)
            second, summary = runner.run(
                manifest, output, workers=1, split_depth=2,
            )
            self.assertEqual(summary["completed"], 1)
            self.assertEqual(len(second["entries"]), 3)
            with open(output, encoding="utf-8") as handle:
                self.assertEqual(json.load(handle), second)


if __name__ == "__main__":
    unittest.main()
