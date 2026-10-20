/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ResolutionProperty

/-!
# Transfer of the resolution property along relatively ample morphisms

A morphism of algebraic spaces that admits an invertible relatively ample module
transfers the resolution property from a quasi-compact quasi-separated target to
the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If `Y` is quasi-compact and quasi-separated and has the resolution property, then a
morphism `f : X ⟶ Y` of algebraic spaces admitting some invertible relatively ample
module on `X` transfers the resolution property to `X`. -/
theorem hasResolutionProperty_of_exists_relativelyAmple {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (hY : SheafOfModules.HasResolutionProperty (structureSheaf Y))
    (hL : ∃ L : X.Modules, isInvertibleObject L ∧ RelativelyAmple f L) :
    SheafOfModules.HasResolutionProperty (structureSheaf X) := sorry

end AlgebraicGeometry.AlgebraicSpace
