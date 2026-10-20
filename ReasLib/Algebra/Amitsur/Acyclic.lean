module

public import ReasLib.Algebra.Amitsur.Complex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

@[expose] public section

universe u

namespace Algebra.Amitsur.extended

/-- If the structure map of a commutative algebra admits an algebra retraction, then its
extended Amitsur cochain complex with coefficients in any module is acyclic. -/
theorem acyclicOfSection (R A M : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] (s : A →ₐ[R] R) :
    (Algebra.Amitsur.extended R A M).Acyclic := sorry

/-- If a commutative algebra is faithfully flat over its base ring, then its extended
Amitsur cochain complex with coefficients in any module is acyclic. -/
theorem acyclicOfFaithfullyFlat (R A M : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] [AddCommGroup M] [Module R M] :
    (Algebra.Amitsur.extended R A M).Acyclic := sorry

end Algebra.Amitsur.extended
