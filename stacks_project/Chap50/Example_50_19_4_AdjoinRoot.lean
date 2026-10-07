module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.AdjoinRoot
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Flat

@[expose] public section

open AlgebraicGeometry Polynomial
open scoped Polynomial

noncomputable section

universe u

namespace Polynomial.MonicDegreeEq

variable {A : Type u} [CommRing A]

/-- The leading-coefficient and degree-bound conditions for the polynomial `X ^ d - C a`. -/
theorem binomialMem (d : ℕ+) (a : A) :
    (X ^ (d : ℕ) - C a).coeff d = 1 ∧
      ∀ i > (d : ℕ), (X ^ (d : ℕ) - C a).coeff i = 0 := sorry

/-- The monic polynomial `X ^ d - C a`, bundled with its positive degree `d`. -/
def binomial (d : ℕ+) (a : A) : MonicDegreeEq A d :=
  ⟨X ^ (d : ℕ) - C a, binomialMem d a⟩

/-- The polynomial underlying `binomial d a` is `X ^ d - C a`. -/
theorem coe_binomial (d : ℕ+) (a : A) :
    (binomial d a : A[X]) = X ^ (d : ℕ) - C a := sorry

end Polynomial.MonicDegreeEq

namespace AdjoinRoot

variable {A : Type u} [CommRing A] {d : ℕ}

/-- The spectrum map of an `AdjoinRoot` quotient by a bundled monic polynomial is finite. -/
instance specMapIsFinite (p : Polynomial.MonicDegreeEq A d) :
    IsFinite (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p.1))) := sorry

/-- The spectrum map of an `AdjoinRoot` quotient by a bundled monic polynomial is syntomic. -/
instance specMapSyntomic (p : Polynomial.MonicDegreeEq A d) :
    Syntomic (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p.1))) := sorry

end AdjoinRoot
