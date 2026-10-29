#!/usr/bin/env python3
"""Check the arithmetic in the nonequilibrium and concatenation bounds.

This script is not a proof.  It provides a transparent numerical check of the
closed-form expressions used in the manuscript.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass


@dataclass(frozen=True)
class Inputs:
    n: int
    circuit_degree: float = 3.0
    circuit_prefactor: float = 1.0
    A: float = 100.0
    q0: float = 1.0e-4
    delta: float = 0.1
    success_probability: float = 0.5

    def validate(self) -> None:
        if self.n < 1:
            raise ValueError("n must be at least 1")
        if self.circuit_degree < 0:
            raise ValueError("circuit_degree must be nonnegative")
        if self.circuit_prefactor <= 0:
            raise ValueError("circuit_prefactor must be positive")
        if self.A <= 0 or self.q0 <= 0:
            raise ValueError("A and q0 must be positive")
        if not 0 < self.A * self.q0 < 1:
            raise ValueError("the below-threshold parameter theta=A*q0 must lie in (0,1)")
        if not 0 < self.delta < 1:
            raise ValueError("delta must lie in (0,1)")
        if not 0 < self.success_probability <= 1:
            raise ValueError("success_probability must lie in (0,1]")


def log_circuit_size(x: Inputs) -> float:
    """Return ln L(n) for L(n)=prefactor*n**degree."""
    return math.log(x.circuit_prefactor) + x.circuit_degree * math.log(x.n)


def nonequilibrium_entropy_nats(n: int) -> float:
    """Return ln(4/p_*) with p_*=2**(-n), without underflow."""
    return n * math.log(2.0) + math.log(4.0)


def rare_set_lower_bound_nats(n: int, c: float) -> float:
    """Return d(c || p_*) for p_*=2**(-n).

    The direct formula is safe for the intended moderate n values.  The
    logarithmic form avoids computing ln p_* from a rounded probability.
    """
    if not 0 < c <= 1:
        raise ValueError("c must lie in (0,1]")
    p = math.ldexp(1.0, -n)
    first = c * (math.log(c) + n * math.log(2.0))
    if c == 1.0:
        return first
    second = (1.0 - c) * math.log((1.0 - c) / (1.0 - p))
    return first + second


def required_concatenation_level(x: Inputs) -> tuple[int, float]:
    """Return the smallest integer k satisfying the manuscript's sufficient bound.

    The manuscript requires

        2**k >= [n ln 2 + ln(4 L(n)/(A delta))] / [-ln(A q0)].
    """
    x.validate()
    theta = x.A * x.q0
    numerator = (
        x.n * math.log(2.0)
        + math.log(4.0)
        + log_circuit_size(x)
        - math.log(x.A)
        - math.log(x.delta)
    )
    rhs = max(0.0, numerator / (-math.log(theta)))
    k = 0 if rhs <= 1.0 else math.ceil(math.log2(rhs))
    return k, rhs


def q_upper_bound(x: Inputs, k: int) -> float:
    """Return A^{-1}(A q0)^{2**k}, evaluated in log space."""
    x.validate()
    if k < 0:
        raise ValueError("k must be nonnegative")
    log_q = -math.log(x.A) + (2**k) * math.log(x.A * x.q0)
    return math.exp(log_q)


def nonequilibrium_failure_upper_bound(x: Inputs, k: int) -> float:
    """Return 4 L(n) q_k / p_* in log space."""
    log_bound = (
        math.log(4.0)
        + log_circuit_size(x)
        + math.log(q_upper_bound(x, k))
        + x.n * math.log(2.0)
    )
    return math.exp(log_bound)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--circuit-degree", type=float, default=3.0)
    parser.add_argument("--circuit-prefactor", type=float, default=1.0)
    parser.add_argument("--A", type=float, default=100.0)
    parser.add_argument("--q0", type=float, default=1.0e-4)
    parser.add_argument("--delta", type=float, default=0.1)
    parser.add_argument("--success-probability", type=float, default=0.5)
    args = parser.parse_args()

    x = Inputs(
        n=args.n,
        circuit_degree=args.circuit_degree,
        circuit_prefactor=args.circuit_prefactor,
        A=args.A,
        q0=args.q0,
        delta=args.delta,
        success_probability=args.success_probability,
    )
    x.validate()
    k, rhs = required_concatenation_level(x)

    print(f"n                                  = {x.n}")
    print(f"theta = A*q0                       = {x.A * x.q0:.6g}")
    print(f"ln L(n)                            = {log_circuit_size(x):.12g}")
    print(f"nonequilibrium entropy, nats       = {nonequilibrium_entropy_nats(x.n):.12g}")
    print(
        "rare-set lower bound, nats        = "
        f"{rare_set_lower_bound_nats(x.n, x.success_probability):.12g}"
    )
    print(f"required lower bound on 2^k        = {rhs:.12g}")
    print(f"smallest sufficient k              = {k}")
    print(f"q_k upper bound                    = {q_upper_bound(x, k):.12g}")
    print(
        "nonequilibrium failure upper bound = "
        f"{nonequilibrium_failure_upper_bound(x, k):.12g}"
    )
    print(f"target delta                       = {x.delta:.12g}")


if __name__ == "__main__":
    main()
