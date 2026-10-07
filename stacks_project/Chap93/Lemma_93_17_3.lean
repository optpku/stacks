module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.OverField

/-!
# Affine smoothings of global complete intersections
-/

@[expose]
public section

universe u v

open scoped TensorProduct

namespace IsGlobalCompleteIntersection

/-- Lemma 93.17.3: Let `k` be a field and let `A` be a global complete intersection
over `k`. There exists a flat finite-type `PowerSeries k`-algebra `B` whose special
fibre `B ⧸ Ideal.span {algebraMap PowerSeries.X}` is isomorphic to `A` as a `k`-algebra,
such that the generic fibre `LaurentSeries k ⊗[PowerSeries k] B` is smooth over
`LaurentSeries k`. Here `PowerSeries k` is `k[[t]]` and `LaurentSeries k` is `k((t))`. -/
@[stacks 0E7V]
theorem exists_flat_finiteType_smoothing {k : Type u} [Field k] {A : Type v}
    [CommRing A] [Algebra k A] [IsGlobalCompleteIntersection k A] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra (PowerSeries k) B)
      (_ : Algebra k B) (_ : IsScalarTower k (PowerSeries k) B)
      (_ : Module.Flat (PowerSeries k) B) (_ : Algebra.FiniteType (PowerSeries k) B)
      (e : (B ⧸ Ideal.span {(algebraMap (PowerSeries k) B) (PowerSeries.X : PowerSeries k)}) ≃ₐ[k] A),
      Algebra.Smooth (LaurentSeries k) (LaurentSeries k ⊗[PowerSeries k] B) :=
  sorry

end IsGlobalCompleteIntersection
