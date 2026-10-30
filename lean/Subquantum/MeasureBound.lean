import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

/-!
# Measure-theoretic content of (A4) + (eq:ratioBound)

The manuscript's assumption (A4) asserts that fault histories and
logical-location failure events admit a *macroscopic* configuration-space
representation whose equilibrium measures are Born probabilities, so that
ordinary classical probability tools — in particular, union bounds over
the `L(n)` fault locations — apply. This file does not justify (A4)
physically; it formalizes the mathematical consequence of (A4) combined
with the pilot-wave Radon–Nikodym transport bound of Eq. (eq:ratioBound).

**Theorem** (`failure_bound_measure_theoretic`). Given a measurable space
`Ω` with equilibrium measure `μ` and nonequilibrium measure `ρ`
satisfying the event-level density bound `ρ(E) ≤ C · μ(E)` (the content
of Eq. (eq:ratioBound)), and `L` fault events `B : Fin L → Set Ω`
covering a failure set `F ⊆ ⋃ᵢ Bᵢ`, we have

    ρ(F) ≤ C · ∑ᵢ μ(Bᵢ).

Specializing to `C = 4/p_*` and `μ(Bᵢ) ≤ q_k` for all `i` recovers the
manuscript's `Pr_ρ(failure) ≤ 4·L(n)·q_k / p_*` (Eq. (eq:neqbad)).

What this file does **not** do: justify that fault histories actually
form such a measurable structure, or that the pilot-wave transport
globally preserves the density bound uniformly over the full
configuration space. Those are the physics content of (A4) and the
transport argument; they remain hypotheses of the theorem.

The value of this formalization is to isolate exactly what (A4) is being
asked to buy: an abstract measurable-space + union-bound structure.
Granting that, the failure bound follows by two lines of measure theory.
-/

namespace Subquantum

open MeasureTheory ENNReal

/-- **Measure-theoretic failure bound.**
Combines (eq:ratioBound) — the density bound `ρ ≤ C·μ` at the event level
— with (A4) — the measurable structure of fault events — to give the
manuscript's union-bounded failure estimate Eq. (eq:neqbad).

Hypotheses:
* `μ`, `ρ` are measures on `Ω` (equilibrium and nonequilibrium);
* `hDens`: `ρ E ≤ C · μ E` for every measurable event `E`
  (the content of Eq. (eq:ratioBound));
* `B : Fin L → Set Ω` are the fault events at the `L` logical locations;
* `F ⊆ ⋃ᵢ Bᵢ`: the failure event is covered by the union of fault
  events.

Conclusion: `ρ F ≤ C · ∑ᵢ μ(Bᵢ)`. If `μ(Bᵢ) ≤ q_k` uniformly, this gives
`ρ F ≤ C · L · q_k`, and with `C = 4/p_*` this is Eq. (eq:neqbad). -/
theorem failure_bound_measure_theoretic
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ρ : Measure Ω)
    (C : ℝ≥0∞)
    (hDens : ∀ E : Set Ω, ρ E ≤ C * μ E)
    {L : ℕ} (B : Fin L → Set Ω)
    {F : Set Ω} (hF : F ⊆ ⋃ i, B i) :
    ρ F ≤ C * ∑ i, μ (B i) :=
  calc ρ F
      ≤ ρ (⋃ i, B i) := measure_mono hF
    _ ≤ C * μ (⋃ i, B i) := hDens _
    _ ≤ C * ∑ i, μ (B i) :=
        mul_le_mul_right (measure_iUnion_fintype_le μ B) C

/-- **Uniform per-location bound.** Specialization: if every per-location
measure `μ(Bᵢ)` is bounded by `q`, then `ρ F ≤ C · L · q`. This is the
form in which the manuscript applies the bound. -/
theorem failure_bound_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ρ : Measure Ω)
    (C : ℝ≥0∞) (q : ℝ≥0∞)
    (hDens : ∀ E : Set Ω, ρ E ≤ C * μ E)
    {L : ℕ} (B : Fin L → Set Ω)
    (hUnif : ∀ i, μ (B i) ≤ q)
    {F : Set Ω} (hF : F ⊆ ⋃ i, B i) :
    ρ F ≤ C * (L : ℝ≥0∞) * q := by
  have hsum : ∑ i, μ (B i) ≤ (L : ℝ≥0∞) * q := by
    calc ∑ i : Fin L, μ (B i)
        ≤ ∑ _ : Fin L, q := Finset.sum_le_sum fun i _ => hUnif i
      _ = (L : ℝ≥0∞) * q := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
  calc ρ F
      ≤ C * ∑ i, μ (B i) :=
        failure_bound_measure_theoretic μ ρ C hDens B hF
    _ ≤ C * ((L : ℝ≥0∞) * q) := mul_le_mul_right hsum C
    _ = C * (L : ℝ≥0∞) * q := (mul_assoc _ _ _).symm

end Subquantum
