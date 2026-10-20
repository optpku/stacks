module

public import ReasLib.Algebra.Module.Devissage.Complete

universe u

#check (Module.Devissage.Complete :
  (R : Type u) → [CommRing R] → (S : FGAlgCat.{u} R) →
    FGModuleCat.{u} S.obj → PrimeSpectrum R → Type (u + 1))
