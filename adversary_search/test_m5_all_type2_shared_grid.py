#!/usr/bin/env python3

import unittest

import m5_all_type2_shared_grid as shared
import m5_type2_coupled_grid as single
import rudin_generator


class AllType2SharedGridTests(unittest.TestCase):
    def test_groups_join_corresponding_stage_roles(self):
        expected = [[], [], []]
        for stage in range(5):
            for role, group in enumerate(single.stage_groups(stage)):
                expected[role].extend(group)
        self.assertEqual(
            shared.GROUPS,
            tuple(tuple(group) for group in expected),
        )
        self.assertEqual(tuple(map(len, shared.GROUPS)), (25, 20, 5))

    def test_mutation_is_exact(self):
        base = rudin_generator.published_jobs()
        config = (9995, 10005, 10000)
        jobs = shared.mutate(base, config)
        factors = {index: 10000 for index in range(len(base))}
        for group, numerator in zip(shared.GROUPS, config):
            for index in group:
                factors[index] = numerator
        self.assertTrue(all(
            jobs[index] == job * factors[index]
            for index, job in enumerate(base)
        ))

    def test_small_grid_is_deterministic(self):
        base = rudin_generator.published_jobs()
        first = shared.enumerate_candidates(
            base, numerators=(9995, 10000, 10005),
        )
        second = shared.enumerate_candidates(
            base, numerators=(9995, 10000, 10005),
        )
        self.assertEqual(first, second)
        self.assertEqual(first["candidate_count"], 26)
        self.assertEqual(
            first["escaped"] + first["survivor_count"], 26,
        )


if __name__ == "__main__":
    unittest.main()
