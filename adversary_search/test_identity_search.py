import unittest

import identity_search


class IdentitySearchTests(unittest.TestCase):
    def test_build_geo_jobs_uses_machine_count(self):
        self.assertEqual(len(identity_search.build_geo_jobs("0.2", "2", 3, m=5)), 16)

    def test_fkt_regression_m4(self):
        value, _, _ = identity_search.eval_value("0.2071067811865475",
                                                   "2.4142135623730951",
                                                   2, m=4)
        self.assertAlmostEqual(value, 1.0 + 2.0 ** -0.5, places=6)


if __name__ == "__main__":
    unittest.main()
