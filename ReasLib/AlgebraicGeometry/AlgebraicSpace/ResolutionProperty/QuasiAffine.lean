module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ResolutionProperty

/-!
# Transfer of the resolution property along quasi-affine morphisms

A quasi-affine morphism of algebraic spaces transfers the resolution property from
a quasi-compact quasi-separated target to the source. The affine case is the
corresponding special case.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If `Y` is quasi-compact and quasi-separated and has the resolution property, then a
quasi-affine morphism `f : X ⟶ Y` of algebraic spaces transfers the resolution property
to `X`. -/
theorem hasResolutionProperty_of_quasiAffine {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiAffine f]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (hY : SheafOfModules.HasResolutionProperty (structureSheaf Y)) :
    SheafOfModules.HasResolutionProperty (structureSheaf X) := sorry

/-- If `Y` is quasi-compact and quasi-separated and has the resolution property, then an
affine morphism `f : X ⟶ Y` of algebraic spaces transfers the resolution property to
`X`. -/
theorem hasResolutionProperty_of_affine {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (hY : SheafOfModules.HasResolutionProperty (structureSheaf Y)) :
    SheafOfModules.HasResolutionProperty (structureSheaf X) := sorry

end AlgebraicGeometry.AlgebraicSpace
