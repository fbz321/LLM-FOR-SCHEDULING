#!/usr/bin/env python3

import unittest

import m5_initial_coupled_grid as coupled
import rudin_generator


class InitialCoupledGridTests(unittest.TestCase):
    def test_groups_partition_initial_jobs(self):
        self.assertEqual(
            tuple(index for group in coupled.GROUPS for index in group),
            tuple(range(15)),
        )

    def test_mutation_is_exact(self):
        base = rudin_generator.published_jobs()
        config = (9995, 10005, 10000)
        jobs = coupled.mutate(base, config)
        factors = {index: 10000 for index in range(len(base))}
        for group, numerator in zip(coupled.GROUPS, config):
            for index in group:
                factors[index] = numerator
        self.assertTrue(all(
            jobs[index] == job * factors[index]
            for index, job in enumerate(base)
        ))

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
