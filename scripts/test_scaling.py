from __future__ import annotations

import math
import unittest

from scripts.check_scaling import (
    Inputs,
    log_nonequilibrium_failure_upper_bound,
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
            self.assertLessEqual(
                log_nonequilibrium_failure_upper_bound(x, k),
                math.log(x.delta),
            )

    def test_previous_level_can_fail_sufficient_condition(self) -> None:
        x = Inputs(n=100, circuit_degree=3.0, A=100.0, q0=1e-4, delta=0.1)
        k, _ = required_concatenation_level(x)
        self.assertGreaterEqual(k, 1)
        self.assertGreater(
            log_nonequilibrium_failure_upper_bound(x, k - 1),
            math.log(x.delta),
        )

    def test_large_n_log_form_is_finite(self) -> None:
        """Regression for the underflow in the previous `q_upper_bound` path.

        Before this fix, `nonequilibrium_failure_upper_bound(n=1000, k=8)`
        raised `ValueError: math domain error` because `q_upper_bound`
        underflowed to 0.0 and the caller then applied `math.log`. The
        mathematical failure bound is finite (~4.3e-204) and the log-form
        output must reflect that.
        """
        x = Inputs(n=1000, circuit_degree=3.0, A=100.0, q0=1e-4, delta=0.1)
        k, _ = required_concatenation_level(x)
        log_bound = log_nonequilibrium_failure_upper_bound(x, k)
        self.assertTrue(math.isfinite(log_bound))
        self.assertLessEqual(log_bound, math.log(x.delta))
        # Sanity check against the independently computed value:
        # log(4.286e-204) ≈ -468.5.
        self.assertAlmostEqual(log_bound, -468.5, places=0)


if __name__ == "__main__":
    unittest.main()
