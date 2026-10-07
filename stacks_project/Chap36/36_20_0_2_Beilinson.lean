module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.EndomorphismAlgebra

universe u

#check (AlgebraicGeometry.ProjectiveSpace.Beilinson.toEnd_bijective :
  ∀ (A : Type u) [CommRing A] (n : ℕ),
    Function.Bijective (AlgebraicGeometry.ProjectiveSpace.Beilinson.toEnd A n))
