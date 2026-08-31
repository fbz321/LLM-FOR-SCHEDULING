#!/usr/bin/env python3

import unittest

import m5_type2_coupled_grid as coupled
import rudin_generator


class Type2CoupledGridTests(unittest.TestCase):
    def test_stage_groups_cover_published_blocks(self):
        self.assertEqual(coupled.stage_groups(0), (
            (15, 16, 17, 18, 19),
            (20, 21, 22, 23),
            (24,),
        ))
        self.assertEqual(coupled.stage_groups(4), (
            (55, 56, 57, 58, 59),
            (60, 61, 62, 63),
            (64,),
        ))

    def test_mutation_is_exact_and_local_after_global_scaling(self):
        base = rudin_generator.published_jobs()
        config = (9995, 10005, 10000)
        jobs = coupled.mutate(base, 2, config)
        factors = {index: 10000 for index in range(len(base))}
        for group, numerator in zip(coupled.stage_groups(2), config):
            for index in group:
                factors[index] = numerator
        self.assertTrue(all(
            jobs[index] == job * factors[index]
            for index, job in enumerate(base)
        ))

    def test_invalid_shapes_are_rejected(self):
        base = rudin_generator.published_jobs()
        with self.assertRaisesRegex(ValueError, "stage"):
            coupled.mutate(base, 5, (1, 1, 1))
        with self.assertRaisesRegex(ValueError, "three"):
            coupled.mutate(base, 0, (1, 1))

    def test_small_grid_is_deterministic(self):
        base = rudin_generator.published_jobs()
        first = coupled.enumerate_candidates(
            base, numerators=(9995, 10000, 10005),
        )
        second = coupled.enumerate_candidates(
            base, numerators=(9995, 10000, 10005),
        )
        self.assertEqual(first, second)
        self.assertEqual(first["candidate_count"], 5 * 26)
        self.assertEqual(
            first["escaped"] + first["survivor_count"], 5 * 26,
        )


if __name__ == "__main__":
    unittest.main()
