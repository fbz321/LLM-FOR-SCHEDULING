import unittest

from parallel_opt import (
    basic_lower_bound,
    build_frontier,
    exact_opt,
    feasible_state,
    lpt_upper_bound,
    schedule_feasible,
)


class ParallelOptTests(unittest.TestCase):
    def test_known_nontrivial_instance(self):
        jobs = (8, 7, 6, 5, 4, 3, 2, 1)
        self.assertEqual(exact_opt(jobs, 3, workers=1, split_depth=3).optimum, 12)
        self.assertEqual(exact_opt(jobs, 3, workers=2, split_depth=3).optimum, 12)

    def test_decision_and_bounds(self):
        jobs = (10, 9, 8, 7, 6, 5)
        self.assertEqual(basic_lower_bound(jobs, 2), 23)
        self.assertEqual(lpt_upper_bound(jobs, 2), 23)
        self.assertTrue(schedule_feasible(jobs, 2, 23, workers=1, split_depth=2))
        self.assertFalse(schedule_feasible(jobs, 2, 22, workers=1, split_depth=2))

    def test_frontier_is_canonical_and_complete(self):
        frontier = build_frontier((5, 4, 3), 2, 3, 100)
        self.assertEqual(len(frontier), 4)
        self.assertEqual(len(set(frontier)), len(frontier))
        self.assertTrue(all(tuple(sorted(state)) == state for state in frontier))
        self.assertTrue(all(sum(state) == 12 for state in frontier))

    def test_capacity_rejects_overloaded_initial_state(self):
        self.assertFalse(feasible_state((1,), (6, 0), 5))


if __name__ == "__main__":
    unittest.main()
