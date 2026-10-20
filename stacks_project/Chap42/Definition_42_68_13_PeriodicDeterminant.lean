module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant

universe u v

#check (CategoryTheory.TwoPeriodicEndomorphism.determinant :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    (K : CategoryTheory.TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hM : IsFiniteLength R K.X) (hK : K.toCochainComplex.Acyclic),
    (IsLocalRing.ResidueField R)ˣ)
