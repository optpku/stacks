/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Limits
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

/-! # Derived modules on algebraic spaces

The original coefficient universe is retained. Left exact sheafification is backed by
restriction to the displayed atlas site, its small-site plus construction, and its specified
right Kan extension, so the derived cell models require no extra geometric input.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Module sheaves carry the homology structure of their abelian category. -/
instance modulesCategoryWithHomology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    CategoryWithHomology X.Modules := CategoryTheory.categoryWithHomology_of_abelian

/-- The standard derived-category structure on `𝒪_X`-modules on an algebraic space. -/
@[reducible]
def modulesHasDerivedCategory {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasDerivedCategory (Modules X) :=
  HasDerivedCategory.standard (Modules X)

/-- The standard derived category of module sheaves for the selected abelian structure. -/
instance modulesHasDerivedCategoryOfAbelian {S : Scheme.{u}} (X : AlgebraicSpace S)
    [Abelian X.Modules] : HasDerivedCategory X.Modules :=
  HasDerivedCategory.standard X.Modules

/-- The unbounded derived category `D(𝒪_X)` of module sheaves on an algebraic space. -/
abbrev ModuleDerived {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  DerivedCategory (Modules X)

/-- The property that every cohomology sheaf of a derived `𝒪_X`-module is quasi-coherent. -/
abbrev derivedQuasiCoherentModuleProperty {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ObjectProperty (ModuleDerived X) :=
  DerivedCategory.cohomologyIn (quasiCoherentModuleProperty X)

/-- The derived category of `𝒪_X`-modules with quasi-coherent cohomology sheaves. -/
abbrev DerivedQCoh {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  DerivedCategory.CohomologyIn (quasiCoherentModuleProperty X)

namespace DerivedQCoh

/-- The inclusion of derived modules with quasi-coherent cohomology into `D(𝒪_X)`. -/
abbrev inclusion {S : Scheme.{u}} (X : AlgebraicSpace S) :
    DerivedQCoh X ⥤ ModuleDerived X :=
  (derivedQuasiCoherentModuleProperty X).ι

/-- An object of `D(𝒪_X)` lies in `DerivedQCoh X` iff every cohomology sheaf is
quasi-coherent. -/
theorem mem_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) :
    derivedQuasiCoherentModuleProperty X E ↔
      ∀ n : ℤ, quasiCoherentModuleProperty X
        ((DerivedCategory.homologyFunctor (Modules X) n).obj E) := sorry

end DerivedQCoh

end AlgebraicGeometry.AlgebraicSpace
