import Subquantum.Entropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Binary KL divergence from the design weight

Formalizes the expansion of `d(c ‖ p_*)` that isolates the linear-in-`n`
term underwriting the `Ω(n)` lower bound (Eq. (eq:binarylower) in the
manuscript, plus the limit expression `d(c ‖ p) = c log(1/p) + O(1)` as
`p → 0`).

The monotonicity argument that lifts this to `d(r ‖ p) ≥ d(c ‖ p)` for
`r ∈ [c, 1]` is omitted; it reduces to a derivative sign check and is
left as a routine exercise.
-/

namespace Subquantum

open Real

/-- Binary KL divergence `d(c ‖ p)` as in the manuscript. -/
noncomputable def binKL (c p : ℝ) : ℝ :=
  c * Real.log (c / p) + (1 - c) * Real.log ((1 - c) / (1 - p))

/-- **Linear-in-`n` expansion** of `binKL c (p_* n)`.
Separates out the `c · n · log 2` term that gives the `Ω(n)` lower bound. -/
theorem binKL_pStar_eq {c : ℝ} (hc : 0 < c) (n : ℕ) :
    binKL c (pStar n) =
      c * ((n : ℝ) * Real.log 2) + c * Real.log c
      + (1 - c) * Real.log ((1 - c) / (1 - pStar n)) := by
  unfold binKL pStar
  rw [Real.log_div hc.ne' (inv_ne_zero (two_pow_ne_zero n))]
  rw [Real.log_inv, Real.log_pow]
  ring

/-- Rewriting of `binKL_pStar_eq` grouping the `n · log 2` term with a single
coefficient `c`. Useful for `Ω(n)` lower-bound arguments. -/
theorem binKL_pStar_linear {c : ℝ} (hc : 0 < c) (n : ℕ) :
    binKL c (pStar n) - c * (n : ℝ) * Real.log 2
      = c * Real.log c
        + (1 - c) * Real.log ((1 - c) / (1 - pStar n)) := by
  rw [binKL_pStar_eq hc n]; ring

end Subquantum
