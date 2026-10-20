module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic

@[expose] public section

open AlgebraicGeometry Polynomial

universe u

namespace AdjoinRoot

variable {A : Type u} [CommRing A] {d : ℕ}

/-- The spectrum map of an `AdjoinRoot` quotient by a bundled monic polynomial is finite. -/
instance specMapIsFinite (p : Polynomial.MonicDegreeEq A d) :
    IsFinite (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p.1))) := sorry

/-- The spectrum map of an `AdjoinRoot` quotient by a bundled monic polynomial is syntomic. -/
instance specMapSyntomic (p : Polynomial.MonicDegreeEq A d) :
    Syntomic (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p.1))) := sorry

end AdjoinRoot
