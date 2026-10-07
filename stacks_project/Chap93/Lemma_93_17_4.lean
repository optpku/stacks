module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.OverField

/-!
# Affine smoothings of finite-dimensional local complete intersections
-/

@[expose]
public section

universe u v

open scoped TensorProduct

namespace IsLocalCompleteIntersection

/-- Lemma 93.17.4: Let `k` be a field and let `A` be a finite-dimensional `k`-algebra
which is a local complete intersection over `k`. There exists a finite flat
`PowerSeries k`-algebra `B` whose special fibre
`B ⧸ Ideal.span {algebraMap PowerSeries.X}` is isomorphic to `A` as a `k`-algebra,
such that the generic fibre `LaurentSeries k ⊗[PowerSeries k] B` is étale over
`LaurentSeries k`. Here `PowerSeries k` is `k[[t]]` and `LaurentSeries k` is `k((t))`. -/
@[stacks 0E7W]
theorem exists_flat_finite_etale_smoothing {k : Type u} [Field k] {A : Type v}
    [CommRing A] [Algebra k A] [FiniteDimensional k A] [IsLocalCompleteIntersection k A] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra (PowerSeries k) B)
      (_ : Algebra k B) (_ : IsScalarTower k (PowerSeries k) B)
      (_ : Module.Flat (PowerSeries k) B) (_ : Module.Finite (PowerSeries k) B)
      (e : (B ⧸ Ideal.span {(algebraMap (PowerSeries k) B) (PowerSeries.X : PowerSeries k)}) ≃ₐ[k] A),
      Algebra.Etale (LaurentSeries k) (LaurentSeries k ⊗[PowerSeries k] B) :=
  sorry

end IsLocalCompleteIntersection
