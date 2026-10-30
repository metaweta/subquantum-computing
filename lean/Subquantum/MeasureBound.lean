import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Tactic

/-!
# Pilot-wave Radon–Nikodym transport (Lemma 2 + Theorem 1 of manuscript)

The manuscript isolates its pilot-wave content as a transfer principle
(Section 6, Lemma 2 "Event-bound transport" and Theorem 1 "Equilibrium-
to-nonequilibrium robustness transfer"): if `ρ ≪ μ` with pointwise
Radon–Nikodym derivative `dρ/dμ ≤ C` under common Bohmian transport,
then at the event level `ρ_t(B) ≤ C · μ_t(B)` for every measurable `B`;
specializing to the conditioned nonequilibrium ensemble gives `C = 4/p_*`
and the robustness-transfer bound `ρ_T(F) ≤ (4/p_*) · μ_T(F)` for any
final failure event `F`.

This file formalizes the measure-theoretic step from the pointwise
density bound to the event-level density bound — Lemma 2 of the
manuscript. The pointwise bound itself is a hypothesis (justified in the
manuscript by the common continuity equation for `ρ_t` and `μ_t = |Ψ_t|²`
under the Bohmian velocity field).

What this file does **not** do: justify the pointwise density bound,
or the common-transport hypothesis itself. Those are the physical
content of the pilot-wave formalism.

For completeness this file also provides lemmas that compose the event
bound with a classical union bound over fault events
(`failure_bound_measure_theoretic`, `failure_bound_uniform`,
`failure_bound_from_rnDeriv`). The manuscript's transfer-principle
framing does *not* use these — all fault-path bookkeeping is delegated
to the conventional FT input of Eq. (eq:FTinput) — but they remain
available for anyone who prefers the explicit enumeration form.
-/

namespace Subquantum

open MeasureTheory ENNReal

/-! ### Lemma 2 (Event-bound transport)

The step from pointwise Radon–Nikodym bound to event-level bound is the
content of the manuscript's Lemma 2 (`lem:eventtransport`). It is a
one-line measure-theoretic fact once stated at the right level of
abstraction. -/

/-- **Lemma 2 (Event-bound transport), manuscript `lem:eventtransport`.**
If `ρ ≪ μ` and `rnDeriv ρ μ ≤ C` holds `μ`-almost everywhere, then
`ρ(E) ≤ C · μ(E)` for every set `E`. Specializing to `C = 4/p_*` and
to a final failure event `F` gives Theorem 1 (`thm:transfer`),
`ρ_T(F) ≤ (4/p_*) · μ_T(F)`. -/
theorem event_bound_of_rnDeriv_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ρ : Measure Ω) [SigmaFinite μ] [ρ.HaveLebesgueDecomposition μ]
    (hAC : ρ ≪ μ) (C : ℝ≥0∞)
    (hBound : ∀ᵐ x ∂μ, ρ.rnDeriv μ x ≤ C)
    (E : Set Ω) :
    ρ E ≤ C * μ E := by
  calc ρ E
      = ∫⁻ x in E, ρ.rnDeriv μ x ∂μ :=
        (Measure.setLIntegral_rnDeriv hAC E).symm
    _ ≤ ∫⁻ _ in E, C ∂μ := by
        refine setLIntegral_mono_ae aemeasurable_const ?_
        exact hBound.mono fun _ hx _ => hx
    _ = C * μ E := setLIntegral_const E C

/-! ### Union-bound layer (not used by the manuscript's transfer principle)

These lemmas combine Lemma 2 with a classical union bound over fault
events. The manuscript's transfer principle (Theorem 1) deliberately
avoids this layer: all enumeration of fault paths is delegated to the
conventional FT input `ε_k(n) ≤ L(n) · q_k`. The union-bound layer
below is kept because it is a correct derivation of the earlier version
of the paper's `4·L(n)·q_k/p_*` bound. -/

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

/-- **End-to-end measure-theoretic failure bound.**
Combines the Radon–Nikodym step (manuscript Eq. (eq:ratioBound),
pointwise ⟹ event-level) with the union-bound step (eq:union) to give
Eq. (eq:neqbad):

given `ρ ≪ μ` with `rnDeriv ρ μ ≤ C` μ-a.e., and fault events
`B : Fin L → Set Ω` covering a failure event `F ⊆ ⋃ᵢ Bᵢ`,

    `ρ(F) ≤ C · ∑ᵢ μ(Bᵢ)`.

The physical input to this chain is just: (i) a pilot-wave transport
argument that preserves the pointwise density bound on `rnDeriv ρ μ`,
and (ii) the (A4) assertion that fault events are measurable with Born
probabilities. Everything else is measure theory. -/
theorem failure_bound_from_rnDeriv
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ρ : Measure Ω) [SigmaFinite μ] [ρ.HaveLebesgueDecomposition μ]
    (hAC : ρ ≪ μ) (C : ℝ≥0∞)
    (hBound : ∀ᵐ x ∂μ, ρ.rnDeriv μ x ≤ C)
    {L : ℕ} (B : Fin L → Set Ω)
    {F : Set Ω} (hF : F ⊆ ⋃ i, B i) :
    ρ F ≤ C * ∑ i, μ (B i) :=
  failure_bound_measure_theoretic μ ρ C
    (fun E => event_bound_of_rnDeriv_le μ ρ hAC C hBound E) B hF

end Subquantum
