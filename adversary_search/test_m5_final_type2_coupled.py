#!/usr/bin/env python3

import unittest

import m5_final_type2_coupled as coupled
import rudin_generator


class FinalType2CoupledTests(unittest.TestCase):
    def test_mutation_is_exact_and_grouped(self):
        base = rudin_generator.published_jobs()
        config = (9950, 10035, 9950)
        jobs = coupled.mutate(base, config)
        factors = {index: (10000, 10000) for index in range(len(base))}
        for group, numerator in zip(coupled.GROUPS, config):
            for index in group:
                factors[index] = (numerator, 10000)
        self.assertTrue(all(
            jobs[index] == job * factors[index][0] // factors[index][1]
            for index, job in enumerate(base)
        ))

    def test_invalid_multiplier_shapes_are_rejected(self):
        base = rudin_generator.published_jobs()
        with self.assertRaisesRegex(ValueError, "three"):
            coupled.mutate(base, (1, 2))
        with self.assertRaisesRegex(ValueError, "positive"):
            coupled.mutate(base, (1, 2, 0))

    def test_small_grid_is_deterministic(self):
        base = rudin_generator.published_jobs()
        first = coupled.enumerate_candidates(
            base, numerators=(9995, 10000, 10005),
        )
        second = coupled.enumerate_candidates(
            base, numerators=(9995, 10000, 10005),
        )
        self.assertEqual(first, second)
        self.assertEqual(first["candidate_count"], 26)
        self.assertEqual(
            first["escaped"] + first["survivor_count"], 26,
        )


if __name__ == "__main__":
    unittest.main()
