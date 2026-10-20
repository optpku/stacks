module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- The affine cyclic-cover algebra over `A ⊗_k k[[π]]` defined by `x^n = π f`,
where `f` is a unit of `A`. -/
@[reducible]
def ramifiedCyclicCoverAlgebra (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (n : ℕ) (f : Aˣ) :=
  AdjoinRoot (Polynomial.X ^ n - Polynomial.C
    (TensorProduct.tmul k (f : A) (PowerSeries.X : PowerSeries k)))

/-- The distinguished root of `x^n - π f` in the affine cyclic-cover algebra. -/
def ramifiedCyclicCoverRoot (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (n : ℕ) (f : Aˣ) : ramifiedCyclicCoverAlgebra k A n f :=
  AdjoinRoot.root (Polynomial.X ^ n - Polynomial.C
    (TensorProduct.tmul k (f : A) (PowerSeries.X : PowerSeries k)))

/-- The distinguished root in the affine cyclic-cover algebra has `n`th power `π f`. -/
theorem ramifiedCyclicCoverRoot_pow (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (n : ℕ) (f : Aˣ) :
    ramifiedCyclicCoverRoot k A n f ^ n =
      algebraMap (TensorProduct k A (PowerSeries k)) (ramifiedCyclicCoverAlgebra k A n f)
        (TensorProduct.tmul k (f : A) (PowerSeries.X : PowerSeries k)) := sorry

end AlgebraicGeometry.Curve
