import Mathlib.Algebra.Star.BigOperators
import Mathlib.Tactic

/-!
# Error-transparent intertwining identity

Formalizes two of the operator-algebraic derivations from Section 6 of
the manuscript ("An error-transparent encoded pointer interface"):

* `logicalMarker_intertwine` — Eq. (eq:intertwine):
  `Q̃_L · V_a = V_a · Q_L`, derived from the Knill–Laflamme
  orthogonality `V_b† · V_a = δ_{ab} P_C` together with `Q_L · P_C = Q_L`.

* `pow_mul_of_intertwine` — the *polynomial* content of
  Eq. (eq:transparentidentity): given `X · V = V · Y` and `p · V = V · p`,
  we have `(X · p)^n · V = V · (Y · p)^n` for every natural `n`.
  Setting `X = Q̃_L`, `Y = Q_L`, `p = p_y`, `V = V_a` recovers the
  polynomial content of (eq:transparentidentity).

The exponential form of (eq:transparentidentity), namely
`exp(z · Q̃_L · p_y) · V_a = V_a · exp(z · Q_L · p_y)`, follows from
`pow_mul_of_intertwine` by applying the power-series definition of the
operator exponential term-by-term — i.e., pulling the right-multiplication
by `V_a` through a `tsum`, which requires a normed-algebra setting. That
step is not formalized here; the purely algebraic content is.
-/

namespace Subquantum

open scoped BigOperators

/-! ### Intertwining identity (eq:intertwine) -/

variable {A : Type*} [Ring A] [StarRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Full-system logical-marker operator `Q̃_L := Σ_a V_a · Q · V_a†`
(manuscript Eq. (eq:Qtilde)). -/
noncomputable def logicalMarker (V : ι → A) (Q : A) : A :=
  ∑ a, V a * Q * star (V a)

/-- **Intertwining identity (eq:intertwine).**
From the Knill–Laflamme orthogonality `V_b† · V_a = δ_{ab} P`
(manuscript Eq. (eq:KLorthogonal)) together with `Q · P = Q`
(the logical marked-state projector is supported on the code space),
`logicalMarker V Q · V_a = V_a · Q`. -/
theorem logicalMarker_intertwine
    (V : ι → A) (Q P : A) (a : ι)
    (hKL : ∀ b, star (V b) * V a = if b = a then P else 0)
    (hQP : Q * P = Q) :
    logicalMarker V Q * V a = V a * Q := by
  unfold logicalMarker
  rw [Finset.sum_mul]
  calc ∑ b, V b * Q * star (V b) * V a
      = ∑ b, V b * Q * (star (V b) * V a) :=
        Finset.sum_congr rfl fun b _ => by rw [mul_assoc]
    _ = ∑ b, V b * Q * (if b = a then P else 0) :=
        Finset.sum_congr rfl fun b _ => by rw [hKL]
    _ = ∑ b, (if b = a then V b * Q * P else 0) :=
        Finset.sum_congr rfl fun b _ => by rw [mul_ite, mul_zero]
    _ = V a * Q * P := by
        rw [Finset.sum_ite_eq' Finset.univ a]
        simp
    _ = V a * Q := by rw [mul_assoc, hQP]

/-! ### Polynomial transparent identity (algebraic content of eq:transparentidentity) -/

/-- **Polynomial transparent identity.**
Given operators satisfying the intertwining relation `X · V = V · Y`
and the commutation `p · V = V · p` (the pointer `p` acts on a different
tensor factor than the code register), we have
`(X · p)^n · V = V · (Y · p)^n` for every `n`. This is the polynomial
content of Eq. (eq:transparentidentity); the full exponential version
follows by linearity of the exponential power series. -/
theorem pow_mul_of_intertwine {A : Type*} [Ring A]
    (X Y p V : A)
    (hint : X * V = V * Y)
    (hpV : p * V = V * p) :
    ∀ n : ℕ, (X * p) ^ n * V = V * (Y * p) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc (X * p) ^ (n + 1) * V
        = (X * p) ^ n * (X * p) * V := by rw [pow_succ]
      _ = (X * p) ^ n * (X * (p * V)) := by rw [mul_assoc, mul_assoc]
      _ = (X * p) ^ n * (X * (V * p)) := by rw [hpV]
      _ = (X * p) ^ n * (X * V * p) := by rw [mul_assoc]
      _ = (X * p) ^ n * (V * Y * p) := by rw [hint]
      _ = (X * p) ^ n * (V * (Y * p)) := by rw [mul_assoc]
      _ = (X * p) ^ n * V * (Y * p) := by rw [← mul_assoc]
      _ = V * (Y * p) ^ n * (Y * p) := by rw [ih]
      _ = V * ((Y * p) ^ n * (Y * p)) := by rw [mul_assoc]
      _ = V * (Y * p) ^ (n + 1) := by rw [← pow_succ]

/-- **Corollary: the polynomial identity for the manuscript's `Q̃_L V_a = V_a Q_L`.**
Combines `logicalMarker_intertwine` with `pow_mul_of_intertwine` to give the
algebraic content of (eq:transparentidentity) directly: the Knill–Laflamme
orthogonality + `Q·P = Q` + `p · V_a = V_a · p` imply
`(Q̃_L · p)^n · V_a = V_a · (Q_L · p)^n` for every `n`. -/
theorem transparent_pow
    (V : ι → A) (Q P p : A) (a : ι)
    (hKL : ∀ b, star (V b) * V a = if b = a then P else 0)
    (hQP : Q * P = Q)
    (hpV : p * V a = V a * p) (n : ℕ) :
    (logicalMarker V Q * p) ^ n * V a = V a * (Q * p) ^ n :=
  pow_mul_of_intertwine _ _ _ _
    (logicalMarker_intertwine V Q P a hKL hQP) hpV n

end Subquantum
