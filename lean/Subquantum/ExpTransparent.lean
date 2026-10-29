import Mathlib.Analysis.Normed.Algebra.Exponential
import Subquantum.ErrorTransparent

/-!
# Exponential form of the transparent identity

Promotes the polynomial identity `(X · p)^n · V = V · (Y · p)^n` (from
`Subquantum.ErrorTransparent`) to the operator exponential:

    exp(X · p) · V = V · exp(Y · p)

under the manuscript's hypotheses `X · V = V · Y` (intertwining) and
`p · V = V · p` (pointer commutes with code-register ops). This is the
full form of Eq.~(eq:transparentidentity).

The proof uses `HasSum` for the exponential series and transports it
through right- (resp. left-)multiplication by `V` via `HasSum.mul_right`
and `HasSum.mul_left`. Requires a complete normed ℝ-algebra `A`; bounded
operators on a complex Hilbert space satisfy this.
-/

namespace Subquantum

/-- **Exponential form of (eq:transparentidentity).**
Promotes `pow_mul_of_intertwine` to the operator exponential by applying
the power-series `HasSum (fun n => (n!)⁻¹ · x^n) (exp x)` term-by-term,
using `HasSum.mul_right` and `HasSum.mul_left` to pass the multiplication
by `V` through. -/
theorem exp_mul_of_intertwine
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X Y p V : A)
    (hint : X * V = V * Y)
    (hpV : p * V = V * p) :
    NormedSpace.exp (X * p) * V = V * NormedSpace.exp (Y * p) := by
  have hpoly := pow_mul_of_intertwine X Y p V hint hpV
  have hX :
      HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ • (X * p) ^ n)
             (NormedSpace.exp (X * p)) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (X * p)
  have hY :
      HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ • (Y * p) ^ n)
             (NormedSpace.exp (Y * p)) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (Y * p)
  have hXV := hX.mul_right V
  have hVY := hY.mul_left V
  have heq :
      (fun n : ℕ => ((n.factorial : ℝ)⁻¹ • (X * p) ^ n) * V)
        = (fun n : ℕ => V * ((n.factorial : ℝ)⁻¹ • (Y * p) ^ n)) := by
    funext n
    rw [smul_mul_assoc, mul_smul_comm, hpoly]
  rw [heq] at hXV
  exact hXV.unique hVY

end Subquantum
