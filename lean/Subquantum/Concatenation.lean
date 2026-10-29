import Mathlib.Tactic

/-!
# Concatenation master inequality

Formalizes the recurrence used in the fault-tolerance section of the
manuscript (Eq. (eq:recursion), (eq:doubleexp)):

if `q (j+1) ≤ A · q(j)²` for all `j` and `q j ≥ 0`, then

    q k ≤ A⁻¹ · (A · q 0) ^ (2^k)

for every concatenation level `k`. The double-exponential suppression is
what allows `O(log n)` levels to overcome the `O(2^n)` likelihood-ratio
enhancement from the small marked-state weight.
-/

namespace Subquantum

/-- **Concatenation master inequality.**
If per-location error rates satisfy the recursion `q (j+1) ≤ A · q(j)²`
with `A > 0` and all `q j ≥ 0`, then at level `k` we have
`q k ≤ A⁻¹ · (A · q 0) ^ (2^k)`. -/
theorem concatenation_bound {A : ℝ} (hA : 0 < A) {q : ℕ → ℝ}
    (hq : ∀ j, 0 ≤ q j) (hrec : ∀ j, q (j + 1) ≤ A * (q j) ^ 2) :
    ∀ k, q k ≤ A⁻¹ * (A * q 0) ^ (2 ^ k) := by
  intro k
  induction k with
  | zero =>
    show q 0 ≤ A⁻¹ * (A * q 0) ^ (2 ^ 0)
    have h : A⁻¹ * (A * q 0) ^ (2 ^ 0) = q 0 := by
      rw [pow_zero, pow_one, ← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul]
    exact h.ge
  | succ k ih =>
    have hqk : 0 ≤ q k := hq k
    have hAq0 : 0 ≤ A * q 0 := mul_nonneg hA.le (hq 0)
    have hpow : 0 ≤ (A * q 0) ^ (2 ^ k) := pow_nonneg hAq0 _
    have hbnd : 0 ≤ A⁻¹ * (A * q 0) ^ (2 ^ k) :=
      mul_nonneg (inv_nonneg.mpr hA.le) hpow
    have hsq : (q k) ^ 2 ≤ (A⁻¹ * (A * q 0) ^ (2 ^ k)) ^ 2 := by
      rw [sq, sq]
      exact mul_self_le_mul_self hqk ih
    have step1 : q (k + 1) ≤ A * (A⁻¹ * (A * q 0) ^ (2 ^ k)) ^ 2 :=
      (hrec k).trans (mul_le_mul_of_nonneg_left hsq hA.le)
    have step2 :
        A * (A⁻¹ * (A * q 0) ^ (2 ^ k)) ^ 2
          = A⁻¹ * (A * q 0) ^ (2 ^ (k + 1)) := by
      have hAne : A ≠ 0 := hA.ne'
      have hExp : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      rw [hExp, pow_mul]
      field_simp
    exact step1.trans_eq step2

/-- Specialization: with `θ := A · q 0 < 1`, we obtain the manuscript's
`q k ≤ A⁻¹ · θ^(2^k)` double-exponential bound. -/
theorem concatenation_theta {A q0 : ℝ} (hA : 0 < A)
    {q : ℕ → ℝ} (hq : ∀ j, 0 ≤ q j) (hq0_eq : q 0 = q0)
    (hrec : ∀ j, q (j + 1) ≤ A * (q j) ^ 2) :
    ∀ k, q k ≤ A⁻¹ * (A * q0) ^ (2 ^ k) := by
  intro k
  have h := concatenation_bound hA hq hrec k
  rw [hq0_eq] at h
  exact h

end Subquantum
