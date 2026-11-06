import Subquantum.Entropy
import Subquantum.Concatenation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Fault-tolerance theorem: logical structure

Formalizes the **logical core** of the manuscript's "Fault-tolerant
marked-state selection" theorem (Section 7). The physical premises are
inputs:

* the per-location recursion `q (j+1) ≤ A · q j^2` (assumption A3);
* the union bound and likelihood-ratio bound that together yield the
  failure upper bound `4 · L(n) · q k / p_*` (assumptions A1, A2, A4);
* polynomial `L(n)`.

What this file proves is the arithmetic skeleton that *given* these
inputs, the sufficient-level inequality (Eq. (kbound)) implies the
δ-level failure bound, and that polynomial `L(n)` implies a
concatenation level `k = O(log n)` suffices.

The pilot-wave dynamics, basin conditioning giving
`ρ/μ ≤ 4/p_*`, error-transparent intertwining identity, syndrome-
resolved fault model, and union-bound derivation remain outside this
formalization.
-/

namespace Subquantum

open Real

/-- **Failure upper bound.** Eq.~(neqbad) of the manuscript:
`Pr_ρ(failure) ≤ 4 · L(n) · q k / p_*`. The RHS is modeled here. -/
noncomputable def failureUpperBound (L : ℝ) (q : ℕ → ℝ) (n k : ℕ) : ℝ :=
  4 * L * q k / pStar n

lemma failureUpperBound_eq (L : ℝ) (q : ℕ → ℝ) (n k : ℕ) :
    failureUpperBound L q n k = 4 * L * q k * (2 : ℝ) ^ n := by
  unfold failureUpperBound pStar
  field_simp

/-- **Arithmetic core of the fault-tolerance theorem.**
Given the recursion `q (j+1) ≤ A · q j^2` with `0 < A · q 0 < 1`, and a
concatenation level `k` satisfying the sufficient-level inequality
`(n · log 2 + log(4L/(Aδ))) / (-log(A · q 0)) ≤ 2^k`, the failure upper
bound `4 L q k / p_*` is at most `δ`. This is the logical content of
Eq.~(kbound) combined with Eq.~(doubleexp). -/
theorem failureUpperBound_le_delta
    {A q0 : ℝ} (hA : 0 < A) (hq0 : 0 < q0) (hAq0 : A * q0 < 1)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (n k : ℕ)
    {q : ℕ → ℝ} (hq : ∀ j, 0 ≤ q j) (hq0_eq : q 0 = q0)
    (hrec : ∀ j, q (j + 1) ≤ A * (q j) ^ 2)
    (hk : ((n : ℝ) * Real.log 2 + Real.log (4 * L / (A * δ)))
            / (-Real.log (A * q0))
          ≤ ((2 ^ k : ℕ) : ℝ)) :
    failureUpperBound L q n k ≤ δ := by
  set θ : ℝ := A * q0 with hθ_def
  have hθ_pos : 0 < θ := mul_pos hA hq0
  have hlogθ_neg : Real.log θ < 0 := Real.log_neg hθ_pos hAq0
  have hneg_logθ_pos : 0 < -Real.log θ := neg_pos.mpr hlogθ_neg
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hAinv_pos : (0 : ℝ) < A⁻¹ := inv_pos.mpr hA
  have hθk_pos : (0 : ℝ) < θ ^ (2 ^ k) := pow_pos hθ_pos _
  have hqk_bound : q k ≤ A⁻¹ * θ ^ (2 ^ k) :=
    concatenation_theta hA hq hq0_eq hrec k
  -- Enlarge via the concatenation bound.
  have h4L2n_nn : (0 : ℝ) ≤ 4 * L * (2 : ℝ) ^ n := by positivity
  have henlarge :
      4 * L * q k * (2 : ℝ) ^ n ≤ 4 * L * (A⁻¹ * θ ^ (2 ^ k)) * (2 : ℝ) ^ n := by
    have hA_arith : 4 * L * q k * (2 : ℝ) ^ n
        = (4 * L * (2 : ℝ) ^ n) * q k := by ring
    have hB_arith : 4 * L * (A⁻¹ * θ ^ (2 ^ k)) * (2 : ℝ) ^ n
        = (4 * L * (2 : ℝ) ^ n) * (A⁻¹ * θ ^ (2 ^ k)) := by ring
    rw [hA_arith, hB_arith]
    exact mul_le_mul_of_nonneg_left hqk_bound h4L2n_nn
  -- Now show 4 L A⁻¹ · 2^n · θ^(2^k) ≤ δ via log monotonicity.
  have hprod_pos : (0 : ℝ) < 4 * L * (A⁻¹ * θ ^ (2 ^ k)) * (2 : ℝ) ^ n := by
    positivity
  suffices h : 4 * L * (A⁻¹ * θ ^ (2 ^ k)) * (2 : ℝ) ^ n ≤ δ by
    rw [failureUpperBound_eq]
    linarith
  -- Multiply out hk by (-log θ) > 0.
  have hk' : (n : ℝ) * Real.log 2 + Real.log (4 * L / (A * δ))
             ≤ ((2 ^ k : ℕ) : ℝ) * (-Real.log θ) := by
    rw [div_le_iff₀ hneg_logθ_pos] at hk
    exact hk
  -- Reduce goal to logarithmic form.
  rw [← Real.log_le_log_iff hprod_pos hδ]
  -- Simplify log of the product.
  have hA_ne : A ≠ 0 := hA.ne'
  have hL_ne : (4 * L : ℝ) ≠ 0 := by positivity
  have hAinv_ne : (A⁻¹ : ℝ) ≠ 0 := hAinv_pos.ne'
  have hθk_ne : θ ^ (2 ^ k) ≠ 0 := hθk_pos.ne'
  have h2n_ne : ((2 : ℝ) ^ n) ≠ 0 := h2n_pos.ne'
  have hexpand :
      Real.log (4 * L * (A⁻¹ * θ ^ (2 ^ k)) * (2 : ℝ) ^ n)
        = Real.log (4 * L) + (Real.log A⁻¹ + Real.log (θ ^ (2 ^ k)))
          + Real.log ((2 : ℝ) ^ n) := by
    rw [Real.log_mul (by positivity) h2n_ne,
        Real.log_mul hL_ne (by positivity),
        Real.log_mul hAinv_ne hθk_ne]
  rw [hexpand, Real.log_inv, Real.log_pow, Real.log_pow]
  -- Goal: log(4L) + (-log A + ↑(2^k) * log θ) + ↑n * log 2 ≤ log δ
  -- Equivalently: log(4L) - log A + ↑n * log 2 + ↑(2^k) * log θ ≤ log δ
  -- We have hk': ↑n * log 2 + log(4L/(Aδ)) ≤ ↑(2^k) * (-log θ).
  -- And log(4L/(Aδ)) = log(4L) - log(Aδ) = log(4L) - log A - log δ.
  have hAδ_ne : (A * δ : ℝ) ≠ 0 := by positivity
  have hδ_ne : (δ : ℝ) ≠ 0 := hδ.ne'
  have hsplit : Real.log (4 * L / (A * δ))
                = Real.log (4 * L) - Real.log A - Real.log δ := by
    rw [Real.log_div hL_ne hAδ_ne, Real.log_mul hA_ne hδ_ne]
    ring
  rw [hsplit] at hk'
  linarith

/-- **Main fault-tolerance theorem (arithmetic form).**
Given:

* positive constants `A, q0` with `A · q0 < 1` (below-threshold recursion);
* a non-negative error sequence `q` with `q 0 = q0` and
  `q (j+1) ≤ A · q j^2` (concatenated distance-three recursion, A3);
* polynomial location count `L > 0`;
* target failure probability `δ ∈ (0, 1)`,

there exists a concatenation level `k` at which the failure upper bound
`4 L q k / p_*` is at most `δ`. See `main_fault_tolerance_log_bound`
below for the quantitative `k = O(log n)` form.

The nonequilibrium cost is `n log 2 + log 4` by `R_eq` (independent
of `k`). -/
theorem main_fault_tolerance
    {A q0 : ℝ} (hA : 0 < A) (hq0 : 0 < q0) (hAq0 : A * q0 < 1)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (n : ℕ)
    {q : ℕ → ℝ} (hq : ∀ j, 0 ≤ q j) (hq0_eq : q 0 = q0)
    (hrec : ∀ j, q (j + 1) ≤ A * (q j) ^ 2) :
    ∃ k : ℕ, failureUpperBound L q n k ≤ δ := by
  -- Choose k large enough that 2^k ≥ (n log 2 + log(4L/(Aδ))) / (-log(A q0)).
  set θ : ℝ := A * q0 with hθ_def
  have hθ_pos : 0 < θ := mul_pos hA hq0
  have hlogθ_neg : Real.log θ < 0 := Real.log_neg hθ_pos hAq0
  have hneg_logθ_pos : 0 < -Real.log θ := neg_pos.mpr hlogθ_neg
  -- The target bound on 2^k:
  set target : ℝ :=
    ((n : ℝ) * Real.log 2 + Real.log (4 * L / (A * δ)))
      / (-Real.log θ) with htarget_def
  -- Any natural number k with 2^k ≥ target works. Pick k = ⌈target⌉ (or 0 if target ≤ 0).
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (target : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
    by_cases ht : target ≤ 0
    · refine ⟨0, ?_⟩
      simpa using ht.trans (by norm_num : (0 : ℝ) ≤ 1)
    · obtain ⟨k, hk⟩ :=
        pow_unbounded_of_one_lt target (by norm_num : (1 : ℝ) < 2)
      refine ⟨k, ?_⟩
      push_cast
      exact hk.le
  exact ⟨k, failureUpperBound_le_delta hA hq0 hAq0 hL hδ n k hq hq0_eq hrec hk⟩

/-- **Quantitative `k = O(log n)` form of the fault-tolerance theorem.**

Strengthens `main_fault_tolerance` by exhibiting a sufficient `k` for
which `2^k` is bounded by an explicit *linear* function of `n`. Taking
`log₂` of that bound shows `k = O(log n)` for any polynomial `L(n)`
and for fixed `A, q0, δ`, confirming the manuscript's asymptotic
claim in Eq.~(kbound).

Concretely, with
`T := (n · log 2 + log(4L/(Aδ))) / (−log(A q0))` and
`m := ⌈max 0 T⌉ + 1`, the choice `k := Nat.clog 2 m` satisfies
`2^k ≥ m > T`, which feeds into `failureUpperBound_le_delta` to give
the δ-bound, and `2^k ≤ 2m ≤ 2(max 0 T + 2)`, i.e. `2^k` is bounded
by an affine function of `max 0 T`. For polynomial `L(n) = poly(n)`,
`T = Θ(n)` for large `n`, hence `k ≤ ⌈log₂(2(T+2))⌉ = O(log n)`. -/
theorem main_fault_tolerance_log_bound
    {A q0 : ℝ} (hA : 0 < A) (hq0 : 0 < q0) (hAq0 : A * q0 < 1)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (n : ℕ)
    {q : ℕ → ℝ} (hq : ∀ j, 0 ≤ q j) (hq0_eq : q 0 = q0)
    (hrec : ∀ j, q (j + 1) ≤ A * (q j) ^ 2) :
    ∃ k : ℕ,
      failureUpperBound L q n k ≤ δ ∧
      ((2 ^ k : ℕ) : ℝ)
        ≤ 2 * (max (0 : ℝ)
                  (((n : ℝ) * Real.log 2 + Real.log (4 * L / (A * δ)))
                      / (-Real.log (A * q0))) + 2) := by
  set θ : ℝ := A * q0 with hθ_def
  have hθ_pos : 0 < θ := mul_pos hA hq0
  have hlogθ_neg : Real.log θ < 0 := Real.log_neg hθ_pos hAq0
  have hneg_logθ_pos : 0 < -Real.log θ := neg_pos.mpr hlogθ_neg
  set T : ℝ :=
    ((n : ℝ) * Real.log 2 + Real.log (4 * L / (A * δ)))
      / (-Real.log θ) with hT_def
  -- Nat.ceil(max 0 T) is a natural number ≥ T; add 1 for strict dominance.
  set m : ℕ := Nat.ceil (max (0 : ℝ) T) + 1 with hm_def
  have hm_pos : 1 ≤ m := by
    rw [hm_def]; exact Nat.succ_le_succ (Nat.zero_le _)
  -- Choose k := Nat.clog 2 m. Then 2^k ≥ m.
  refine ⟨Nat.clog 2 m, ?_, ?_⟩
  · -- failure bound: use failureUpperBound_le_delta with 2^k ≥ T.
    apply failureUpperBound_le_delta hA hq0 hAq0 hL hδ n _ hq hq0_eq hrec
    have hT_le_m : T ≤ (m : ℝ) := by
      rw [hm_def]
      push_cast
      have h1 : T ≤ max (0 : ℝ) T := le_max_right _ _
      have h2 : max (0 : ℝ) T ≤ (Nat.ceil (max (0 : ℝ) T) : ℝ) := Nat.le_ceil _
      linarith
    have hm_le_pow : (m : ℝ) ≤ ((2 ^ Nat.clog 2 m : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_pow_clog (by norm_num : (1 : ℕ) < 2) m
    exact hT_le_m.trans hm_le_pow
  · -- upper bound: 2^(clog 2 m) ≤ 2m ≤ 2(T + 2).
    -- First: 2^(clog 2 m) ≤ 2 * m. By Nat.clog_le_iff_le_pow it suffices
    -- to show m ≤ 2^k implies the bound; we use the elementary fact that
    -- for m ≥ 1 the smallest k with 2^k ≥ m satisfies 2^k < 2m.
    have hclog_pow_le : (2 ^ Nat.clog 2 m : ℕ) ≤ 2 * m := by
      -- Equivalent: Nat.clog 2 m ≤ Nat.clog 2 (2 * m), and 2 * m = 2^1 * m ≥ 2^k ...
      -- We prove by cases on m = 1 vs m ≥ 2.
      rcases Nat.lt_or_ge m 2 with hm_lt | hm_ge
      · -- m ∈ {0, 1}. m ≥ 1 by hm_pos, so m = 1, clog 2 1 = 0.
        interval_cases m
        · simp [Nat.clog]
      · -- m ≥ 2: clog 2 m ≤ Nat.log 2 m + 1, and 2^(log 2 m) ≤ m, so 2^clog ≤ 2m.
        have hlog_pow_le : (2 ^ Nat.log 2 m : ℕ) ≤ m :=
          Nat.pow_log_le_self 2 (Nat.one_le_iff_ne_zero.mp hm_pos)
        -- Nat.clog_le_iff_le_pow: clog 2 m ≤ Nat.log 2 m + 1 iff m ≤ 2 ^ (Nat.log 2 m + 1).
        have hclog_le : Nat.clog 2 m ≤ Nat.log 2 m + 1 := by
          rw [Nat.clog_le_iff_le_pow (by norm_num : (1 : ℕ) < 2)]
          calc m ≤ 2 * (2 ^ Nat.log 2 m) := by
                have h2 := hlog_pow_le
                -- Direct: m < 2 * 2^(log 2 m) is standard; but here we just need ≤.
                -- Use: m ≤ 2^(⌈log⌉) ≤ 2 * 2^(⌊log⌋).
                have hmpos : 0 < m := hm_pos
                have := Nat.lt_pow_succ_log_self (by norm_num : (1 : ℕ) < 2) m
                omega
            _ = 2 ^ (Nat.log 2 m + 1) := by
                rw [pow_succ]; ring
        calc (2 ^ Nat.clog 2 m : ℕ)
            ≤ 2 ^ (Nat.log 2 m + 1) := Nat.pow_le_pow_right (by norm_num) hclog_le
          _ = 2 * 2 ^ Nat.log 2 m := by rw [pow_succ]; ring
          _ ≤ 2 * m := by exact Nat.mul_le_mul_left 2 hlog_pow_le
    -- Convert to ℝ and finish.
    have h1 : ((2 ^ Nat.clog 2 m : ℕ) : ℝ) ≤ (2 * m : ℕ) := by
      exact_mod_cast hclog_pow_le
    have h2 : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    rw [h2] at h1
    have h3 : (m : ℝ) ≤ max (0 : ℝ) T + 2 := by
      rw [hm_def]
      push_cast
      have h4 : (Nat.ceil (max (0 : ℝ) T) : ℝ) ≤ max (0 : ℝ) T + 1 :=
        (Nat.ceil_lt_add_one (le_max_left _ _)).le
      linarith
    linarith [mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 2)]

end Subquantum
