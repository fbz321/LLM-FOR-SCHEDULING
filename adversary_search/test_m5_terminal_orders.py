#!/usr/bin/env python3

import unittest

import m5_terminal_orders as orders
import rudin_generator


class TerminalOrderTests(unittest.TestCase):
    def test_all_unique_orders_preserve_multiset(self):
        base = rudin_generator.published_jobs()
        variants = orders.unique_terminal_orders(base)
        self.assertEqual(len(variants), 30)
        expected = sorted(base[orders.TERMINAL_START:])
        self.assertTrue(all(sorted(order) == expected for order in variants))

    def test_published_order_is_present(self):
        base = rudin_generator.published_jobs()
        payload = orders.enumerate_candidates(base)
        labels = {record["order"] for record in payload["candidates"]}
        self.assertIn("AAAASF", labels)
        self.assertEqual(payload["candidate_count"], 30)


if __name__ == "__main__":
    unittest.main()
