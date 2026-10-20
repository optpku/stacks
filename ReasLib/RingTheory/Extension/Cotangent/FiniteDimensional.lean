module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import ReasLib.RingTheory.Extension.Cotangent.ExtOne

@[expose] public section

universe u

namespace RingHom.SquareZeroExtension

/-- A finite type algebra with finite nonsmooth locus has a finite-dimensional first cotangent
extension group in the canonical self-presentation cokernel model. -/
theorem finiteDimensional_extOneNaiveCotangent_of_finite_nonsmooth
    (k : Type u) [Field k] (P : Type u) [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] (_h : (Algebra.smoothLocus k P)ᶜ.Finite) :
    FiniteDimensional k (extOneNaiveCotangent k P P) := sorry

end RingHom.SquareZeroExtension
