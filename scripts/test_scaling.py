from __future__ import annotations

import math
import unittest

from scripts.check_scaling import (
    Inputs,
    nonequilibrium_entropy_nats,
    nonequilibrium_failure_upper_bound,
    rare_set_lower_bound_nats,
    required_concatenation_level,
)


class ScalingTests(unittest.TestCase):
    def test_entropy_formula(self) -> None:
        for n in (1, 10, 100):
            self.assertAlmostEqual(
                nonequilibrium_entropy_nats(n),
                n * math.log(2.0) + math.log(4.0),
            )

    def test_lower_bound_is_linear_asymptotically(self) -> None:
        c = 0.5
        b100 = rare_set_lower_bound_nats(100, c)
        b200 = rare_set_lower_bound_nats(200, c)
        self.assertAlmostEqual(b200 - b100, 50.0 * math.log(2.0), places=10)

    def test_chosen_level_meets_failure_target(self) -> None:
        for n in (10, 50, 100, 500):
            x = Inputs(n=n, circuit_degree=3.0, A=100.0, q0=1e-4, delta=0.1)
            k, _ = required_concatenation_level(x)
            self.assertLessEqual(nonequilibrium_failure_upper_bound(x, k), x.delta)

    def test_previous_level_can_fail_sufficient_condition(self) -> None:
        x = Inputs(n=100, circuit_degree=3.0, A=100.0, q0=1e-4, delta=0.1)
        k, _ = required_concatenation_level(x)
        self.assertGreaterEqual(k, 1)
        self.assertGreater(nonequilibrium_failure_upper_bound(x, k - 1), x.delta)


if __name__ == "__main__":
    unittest.main()
