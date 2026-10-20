module

public import ReasLib.Algebra.Amitsur.Complex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section

universe u

#check (@Algebra.Amitsur.extended :
  (R A M : Type u) → [CommRing R] → [CommRing A] → [Algebra R A] →
    [AddCommGroup M] → [Module R M] → CochainComplex (ModuleCat R) ℕ)
