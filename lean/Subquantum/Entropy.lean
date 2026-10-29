import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Design weight and nonequilibrium relative-entropy cost

Formalizes `p_* = 2^(-n)` and the closed-form `R n = n * log 2 + log 4`
appearing in the manuscript's abstract and main theorem.
-/

namespace Subquantum

open Real

/-- Design weight `p_* = 2^(-n)` associated with one basis state in the
uniform superposition over `n` bits. -/
noncomputable def pStar (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

lemma two_pow_pos (n : ℕ) : (0 : ℝ) < (2 : ℝ) ^ n :=
  pow_pos (by norm_num) n

lemma two_pow_ne_zero (n : ℕ) : ((2 : ℝ) ^ n) ≠ 0 :=
  (two_pow_pos n).ne'

@[simp] lemma pStar_pos (n : ℕ) : 0 < pStar n :=
  inv_pos.mpr (two_pow_pos n)

lemma pStar_ne_zero (n : ℕ) : pStar n ≠ 0 := (pStar_pos n).ne'

/-- Nonequilibrium relative-entropy cost in nats: `R = log(4 / p_*)`.
This is the resource measure used throughout the manuscript. -/
noncomputable def R (n : ℕ) : ℝ := Real.log (4 / pStar n)

/-- **Closed form.** `R n = n · log 2 + log 4`.
This is the linear-in-`n` scaling asserted in the abstract: the nonequilibrium
cost of selecting a marked state of design weight `2^(-n)` is exactly
`n · log 2 + log 4` nats. -/
theorem R_eq (n : ℕ) : R n = (n : ℝ) * Real.log 2 + Real.log 4 := by
  unfold R pStar
  rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
      (inv_ne_zero (two_pow_ne_zero n))]
  rw [Real.log_inv, Real.log_pow]
  ring

/-- Corollary: `R n` differs from `n · log 2` by the constant `log 4`,
confirming the `n·log 2 + O(1)` statement. -/
theorem R_sub_linear_const (n : ℕ) :
    R n - (n : ℝ) * Real.log 2 = Real.log 4 := by
  rw [R_eq]; ring

end Subquantum
