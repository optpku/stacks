module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.Generator

universe u

#check (AlgebraicGeometry.ProjectiveSpace.beilinsonGenerator :
  ∀ (R : Type u) [CommRing R] (n : ℕ),
    (AlgebraicGeometry.ProjectiveSpace.scheme R n).Modules)
