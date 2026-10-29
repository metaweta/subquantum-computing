import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Tactic

/-!
# Syndrome-only transparency (eq:syndromeonly)

Formalizes the algebraic content of the manuscript's syndrome-only
characterization of error-transparent fault operators (Section 6,
Eq. (eq:syndromeonly)).

**Setup.** A code register `H₁` and a syndrome register `H₂`, both
modules over a commutative semiring `𝕜`. The manuscript's isometry
`W : K ≃ C ⊗ H_syn` is modeled as a `LinearEquiv K ≃ₗ[𝕜] H₁ ⊗[𝕜] H₂`.

An operator `S` on the full space `K` is **transparent** if its
`W`-conjugate acts only on the second (syndrome) factor:
`W ∘ S = (id_L ⊗ s) ∘ W` for some `s : H₂ →ₗ[𝕜] H₂`. In the manuscript,
this is `WSW† = I_L ⊗ s` (Eq. (eq:syndromeonly)).

The **encoded pointer operator** acts only on the first (code) factor:
`W ∘ Q̃ = (Q ⊗ id_syn) ∘ W` for some `Q : H₁ →ₗ[𝕜] H₁`. In the
manuscript, this is `WQ̃_LW† = Q_L ⊗ I_syn`.

**Theorem.** Transparent operators commute with encoded pointer operators
on `K`.

The core content lives at the tensor-product level: operators of form
`id ⊗ s` and `Q ⊗ id` commute because both compositions equal `Q ⊗ s`
(by `LinearMap.lTensor_comp_rTensor` and `LinearMap.rTensor_comp_lTensor`).
The `W`-conjugation step is a routine cancellation using the
`LinearEquiv.comp_toLinearMap_eq_iff` lemma for `LinearEquiv`.
-/

namespace Subquantum

open scoped TensorProduct

variable {𝕜 : Type*} [CommSemiring 𝕜]
variable {H1 H2 : Type*}
  [AddCommMonoid H1] [AddCommMonoid H2]
  [Module 𝕜 H1] [Module 𝕜 H2]

/-! ### Core commutation on the tensor product -/

/-- An operator on `H₁ ⊗ H₂` is **syndrome-only** if it acts only on the
second factor, i.e., has the form `id_{H₁} ⊗ s`. -/
def IsSyndromeOnly (S : H1 ⊗[𝕜] H2 →ₗ[𝕜] H1 ⊗[𝕜] H2) : Prop :=
  ∃ s : H2 →ₗ[𝕜] H2, S = LinearMap.lTensor H1 s

/-- An operator on `H₁ ⊗ H₂` is **code-only** if it acts only on the first
factor, i.e., has the form `Q ⊗ id_{H₂}`. -/
def IsCodeOnly (T : H1 ⊗[𝕜] H2 →ₗ[𝕜] H1 ⊗[𝕜] H2) : Prop :=
  ∃ Q : H1 →ₗ[𝕜] H1, T = LinearMap.rTensor H2 Q

/-- **Core commutation lemma.** A syndrome-only operator commutes with a
code-only operator on `H₁ ⊗ H₂`. Both compositions `(id ⊗ s) ∘ (Q ⊗ id)`
and `(Q ⊗ id) ∘ (id ⊗ s)` equal `Q ⊗ s = TensorProduct.map Q s`. -/
theorem commute_of_syndromeOnly_codeOnly
    {S T : H1 ⊗[𝕜] H2 →ₗ[𝕜] H1 ⊗[𝕜] H2}
    (hS : IsSyndromeOnly S) (hT : IsCodeOnly T) :
    S ∘ₗ T = T ∘ₗ S := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨Q, hQ⟩ := hT
  rw [hs, hQ, LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]

/-! ### `W`-pulled-back version (the manuscript's statement on `K`) -/

/-- An operator `S` on `K` is **transparent via `W`** if its `W`-conjugate
on `H₁ ⊗ H₂` is syndrome-only; equivalently (in the manuscript's
notation), `WSW† = I_L ⊗ s`. -/
def IsTransparentVia {K : Type*} [AddCommMonoid K] [Module 𝕜 K]
    (W : K ≃ₗ[𝕜] H1 ⊗[𝕜] H2) (S : K →ₗ[𝕜] K) : Prop :=
  ∃ s : H2 →ₗ[𝕜] H2,
    W.toLinearMap ∘ₗ S = (LinearMap.lTensor H1 s) ∘ₗ W.toLinearMap

/-- An operator `T` on `K` is an **encoded pointer via `W`** if its
`W`-conjugate on `H₁ ⊗ H₂` is code-only; in the manuscript,
`WQ̃_LW† = Q_L ⊗ I_syn`. -/
def IsEncodedPointerVia {K : Type*} [AddCommMonoid K] [Module 𝕜 K]
    (W : K ≃ₗ[𝕜] H1 ⊗[𝕜] H2) (T : K →ₗ[𝕜] K) : Prop :=
  ∃ Q : H1 →ₗ[𝕜] H1,
    W.toLinearMap ∘ₗ T = (LinearMap.rTensor H2 Q) ∘ₗ W.toLinearMap

/-- **Syndrome-only transparency commutation (manuscript's statement).**
If `W : K ≃ₗ H₁ ⊗ H₂` identifies the full physical space `K` with the
tensor product of code and syndrome registers, then any transparent fault
operator (one satisfying `WSW† = I_L ⊗ s`) commutes with any encoded
pointer operator (one satisfying `WQ̃_LW† = Q_L ⊗ I_syn`) on `K`. -/
theorem commute_of_transparent_encoded
    {K : Type*} [AddCommMonoid K] [Module 𝕜 K]
    (W : K ≃ₗ[𝕜] H1 ⊗[𝕜] H2)
    {S T : K →ₗ[𝕜] K}
    (hS : IsTransparentVia W S) (hT : IsEncodedPointerVia W T) :
    S ∘ₗ T = T ∘ₗ S := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨Q, hQ⟩ := hT
  rw [← W.comp_toLinearMap_eq_iff]
  calc W.toLinearMap ∘ₗ (S ∘ₗ T)
      = (W.toLinearMap ∘ₗ S) ∘ₗ T := (LinearMap.comp_assoc _ _ _).symm
    _ = (LinearMap.lTensor H1 s ∘ₗ W.toLinearMap) ∘ₗ T := by rw [hs]
    _ = LinearMap.lTensor H1 s ∘ₗ (W.toLinearMap ∘ₗ T) :=
        LinearMap.comp_assoc _ _ _
    _ = LinearMap.lTensor H1 s ∘ₗ (LinearMap.rTensor H2 Q ∘ₗ W.toLinearMap) := by
        rw [hQ]
    _ = (LinearMap.lTensor H1 s ∘ₗ LinearMap.rTensor H2 Q) ∘ₗ W.toLinearMap :=
        (LinearMap.comp_assoc _ _ _).symm
    _ = (LinearMap.rTensor H2 Q ∘ₗ LinearMap.lTensor H1 s) ∘ₗ W.toLinearMap := by
        rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
    _ = LinearMap.rTensor H2 Q ∘ₗ (LinearMap.lTensor H1 s ∘ₗ W.toLinearMap) :=
        LinearMap.comp_assoc _ _ _
    _ = LinearMap.rTensor H2 Q ∘ₗ (W.toLinearMap ∘ₗ S) := by rw [← hs]
    _ = (LinearMap.rTensor H2 Q ∘ₗ W.toLinearMap) ∘ₗ S :=
        (LinearMap.comp_assoc _ _ _).symm
    _ = (W.toLinearMap ∘ₗ T) ∘ₗ S := by rw [← hQ]
    _ = W.toLinearMap ∘ₗ (T ∘ₗ S) := LinearMap.comp_assoc _ _ _

end Subquantum
