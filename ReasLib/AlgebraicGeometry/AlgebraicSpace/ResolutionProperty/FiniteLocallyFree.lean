/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ResolutionProperty

/-!
# Transfer of the resolution property along finite locally free morphisms

A surjective finite locally free morphism of algebraic spaces transfers the
resolution property from its source to its target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A surjective finite locally free morphism of algebraic spaces transfers the
resolution property from its source to its target. -/
theorem hasResolutionProperty_of_surjective_finiteLocallyFree {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Surjective f] [FiniteLocallyFree f]
    (hX : SheafOfModules.HasResolutionProperty (structureSheaf X)) :
    SheafOfModules.HasResolutionProperty (structureSheaf Y) := sorry

end AlgebraicGeometry.AlgebraicSpace
