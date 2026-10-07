module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Polynomial.Basic

@[expose] public section

noncomputable section

universe u
namespace AlgebraicGeometry.Curve

/-- The affine cyclic-cover algebra over `A ⊗_k k[[π]]` with the prescribed
relation `x^n = π f`, where the unit `f` describes the line-bundle trivialization. -/
def ramifiedCyclicCoverAlgebra (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (n : ℕ) (f : Aˣ) :=
  Polynomial (TensorProduct k A (PowerSeries k)) ⧸
    Ideal.span ({Polynomial.X ^ n - Polynomial.C
      (TensorProduct.tmul k (f : A) (PowerSeries.X : PowerSeries k))} :
        Set (Polynomial (TensorProduct k A (PowerSeries k))))

end AlgebraicGeometry.Curve
