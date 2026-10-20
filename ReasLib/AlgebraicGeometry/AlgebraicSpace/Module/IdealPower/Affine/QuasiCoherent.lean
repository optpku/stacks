module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower.Affine

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

/-- The inverse-image ideal `I 𝒪_X` of an ideal of an affine base is quasi-coherent. -/
instance instIsQuasiCoherent_pullbackIdeal
    {A : Type u} [CommRing A] {I : Ideal A}
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    {f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))} :
    IsQuasiCoherent (pullbackIdeal I f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology
