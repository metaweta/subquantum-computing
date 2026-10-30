import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Constant physical pointer margin (manuscript Lemma 3)

For the exponential-tail realization of the initial survival probability
`S(y) = K · exp(-y/λ)` from Section 4 of the manuscript, the preparation
shell `A_*` (defined by `p_*/4 < S(y) < p_*/2`) sits at constant distance
`m = λ · log 2` from the marked-basin boundary (defined by `S(y_b) = p_*`),
and has width `λ · log 2`.

Both quantities are independent of `n` (equivalently, of `p_* = 2^{-n}`).
This is the content of Lemma 3 (`lem:pointermargin`) in the manuscript;
the file formalizes the two arithmetic identities on which it rests.
-/

namespace Subquantum

open Real

/-- Pointer coordinate obtained by inverting the exponential-tail survival
probability `S(y) = K · exp(-y/λ)`: solving for `y` in terms of `s` gives
`y(s) = λ · log(K/s)`. -/
noncomputable def pointerCoord (K lam s : ℝ) : ℝ := lam * Real.log (K / s)

/-- Difference formula: `y(a) - y(b) = λ · log(b/a)`. Follows from
`log(K/a) - log(K/b) = log(b/a)` by the logarithm quotient law. -/
theorem pointerCoord_sub
    {K lam a b : ℝ} (hK : 0 < K) (ha : 0 < a) (hb : 0 < b) :
    pointerCoord K lam a - pointerCoord K lam b = lam * Real.log (b / a) := by
  unfold pointerCoord
  rw [← mul_sub]
  congr 1
  rw [Real.log_div hK.ne' ha.ne', Real.log_div hK.ne' hb.ne',
      Real.log_div hb.ne' ha.ne']
  ring

/-- **Shell-to-boundary margin (Lemma 3, first half).**
The near edge of the preparation shell (at survival probability `p_*/2`)
sits at distance `λ · log 2` from the marked-basin boundary (at survival
probability `p_*`). The result is independent of `p_*`. -/
theorem shell_margin
    {K lam pStar : ℝ} (hK : 0 < K) (hp : 0 < pStar) :
    pointerCoord K lam (pStar / 2) - pointerCoord K lam pStar
      = lam * Real.log 2 := by
  rw [pointerCoord_sub hK (by positivity) hp]
  congr 1
  have h : pStar / (pStar / 2) = 2 := by field_simp
  rw [h]

/-- **Shell width (Lemma 3, second half).**
The preparation shell between survival probabilities `p_*/4` and `p_*/2`
has width `λ · log 2`. Also independent of `p_*`. -/
theorem shell_width
    {K lam pStar : ℝ} (hK : 0 < K) (hp : 0 < pStar) :
    pointerCoord K lam (pStar / 4) - pointerCoord K lam (pStar / 2)
      = lam * Real.log 2 := by
  rw [pointerCoord_sub hK (by positivity) (by positivity)]
  congr 1
  have h : (pStar / 2) / (pStar / 4) = 2 := by field_simp; norm_num
  rw [h]

end Subquantum
