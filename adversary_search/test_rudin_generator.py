#!/usr/bin/env python3

import json
import os
import tempfile
import unittest

import rudin_generator as generator
import template_schema

HERE = os.path.dirname(os.path.abspath(__file__))
SEED = os.path.join(HERE, "seeds", "rudin2001_m5.json")


class RudinGeneratorTests(unittest.TestCase):
    def test_published_generator_exactly_reproduces_seed(self):
        with open(SEED, encoding="utf-8") as handle:
            seed = json.load(handle)
        generated = generator.published_template()
        seed_sizes, seed_metadata = template_schema.materialize(seed)
        generated_sizes, generated_metadata = template_schema.materialize(generated)
        self.assertEqual(seed_metadata["m"], generated_metadata["m"])
        self.assertEqual(seed_sizes, generated_sizes)
        self.assertEqual(len(generated_sizes), 71)

    def test_all_published_jobs_are_positive_and_deterministic(self):
        first = generator.published_jobs()
        second = generator.published_jobs()
        self.assertEqual(first, second)
        self.assertEqual(len(first), 71)
        self.assertTrue(all(job > 0 for job in first))

    def test_layer_structure_matches_five_type2_and_one_type3(self):
        template = generator.published_template()
        kinds = [layer["kind"] for layer in template["layers"]]
        self.assertEqual(kinds[:3], ["type1"] * 3)
        self.assertEqual(kinds.count("type2-b"), 5)
        self.assertEqual(kinds.count("type2-a"), 5)
        self.assertEqual(kinds.count("type2-singleton"), 5)
        self.assertEqual(kinds.count("type3-a"), 1)
        self.assertEqual(kinds.count("type3-singleton"), 1)

    def test_formula_audit_is_explicitly_non_authoritative(self):
        audit = generator.formula_audit()
        self.assertFalse(audit["authoritative"])
        self.assertEqual(len(audit["rows"]), 6)
        for row in audit["rows"]:
            self.assertEqual(len(row["generated"]), 3)
            self.assertEqual(len(row["absolute_error"]), 3)

    def test_json_round_trip(self):
        with tempfile.TemporaryDirectory() as directory:
            path = os.path.join(directory, "rudin.json")
            generator.atomic_json(path, generator.published_template())
            with open(path, encoding="utf-8") as handle:
                restored = json.load(handle)
            sizes, metadata = template_schema.materialize(restored)
            self.assertEqual(metadata["m"], 5)
            self.assertEqual(len(sizes), 71)

    def test_printed_decimal_scaling_rule(self):
        self.assertEqual(
            generator.printed_decimal_to_integer("3.3286757562613"),
            33286757562613,
        )
        self.assertEqual(
            generator.printed_decimal_to_integer("190001006.704712"),
            1900010067047120000000,
        )


if __name__ == "__main__":
    unittest.main()
