/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Module
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact

/-! # Unbounded derived module functors on étale sites of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Module.Derived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The unbounded derived small étale module direct image in coefficient universe `u + 1`. -/
noncomputable def smallDirectImage (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}]
    [(SheafOfModules.pushforward.{u + 1} (smallChartStructureMap Y)).IsRightAdjoint]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (ringedSite Y))] :
    ModuleDerived.{u + 1} (ringedSite Y) ⥤ ModuleDerived.{u + 1} (ringedSite X) :=
  @Adjunction.Derived.KInjective.right
    (RingedSite.ModuleCat.{u + 1} (ringedSite X))
    (RingedSite.ModuleCat.{u + 1} (ringedSite Y)) _ _ _ _
    (moduleCat_hasDerivedCategory (ringedSite X))
    (moduleCat_hasDerivedCategory (ringedSite Y))
    (etaleSmallModulePushforward f) inferInstance inferInstance

/-- Derived small étale module direct image is the K-injective right-derived geometric pushforward. -/
theorem smallDirectImage_eq (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}]
    [(SheafOfModules.pushforward.{u + 1} (smallChartStructureMap Y)).IsRightAdjoint]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (ringedSite Y))] :
    smallDirectImage f =
      @Adjunction.Derived.KInjective.right
        (RingedSite.ModuleCat.{u + 1} (ringedSite X))
        (RingedSite.ModuleCat.{u + 1} (ringedSite Y)) _ _ _ _
        (moduleCat_hasDerivedCategory (ringedSite X))
        (moduleCat_hasDerivedCategory (ringedSite Y))
        (etaleSmallModulePushforward f) inferInstance inferInstance := rfl

/-- The unbounded derived direct image of modules on big étale slice sites. -/
noncomputable def bigDirectImage (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (Big.ringedSite Y))] :
    ModuleDerived.{u + 1} (Big.ringedSite Y) ⥤
      ModuleDerived.{u + 1} (Big.ringedSite X) :=
  @Adjunction.Derived.KInjective.right
    (RingedSite.ModuleCat.{u + 1} (Big.ringedSite X))
    (RingedSite.ModuleCat.{u + 1} (Big.ringedSite Y)) _ _ _ _
    (moduleCat_hasDerivedCategory (Big.ringedSite X))
    (moduleCat_hasDerivedCategory (Big.ringedSite Y))
    (Module.bigDirectImage f) inferInstance inferInstance

/-- Derived big étale module direct image is K-injective right-derived pushforward. -/
theorem bigDirectImage_eq (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (Big.ringedSite Y))] :
    bigDirectImage f =
      @Adjunction.Derived.KInjective.right
        (RingedSite.ModuleCat.{u + 1} (Big.ringedSite X))
        (RingedSite.ModuleCat.{u + 1} (Big.ringedSite Y)) _ _ _ _
        (moduleCat_hasDerivedCategory (Big.ringedSite X))
        (moduleCat_hasDerivedCategory (Big.ringedSite Y))
        (Module.bigDirectImage f) inferInstance inferInstance := rfl

/-- Postcomposition inverse image on big étale module sheaves is an exact functor. -/
noncomputable def bigInverseImageExact (g : Y ⟶ X) :
    SheafOfModules.{u + 1} (Big.structureSheaf X) ⥤ₑ
      SheafOfModules.{u + 1} (Big.structureSheaf Y) :=
  ⟨Module.bigInverseImage g, sorry⟩

/-- Derived inverse image on big étale module sheaves along postcomposition. -/
noncomputable def bigInverseImage (g : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}] :
    ModuleDerived.{u + 1} (Big.ringedSite X) ⥤
      ModuleDerived.{u + 1} (Big.ringedSite Y) :=
  @ExactFunctor.mapDerivedCategory
    (RingedSite.ModuleCat.{u + 1} (Big.ringedSite X)) _ _
    (moduleCat_hasDerivedCategory (Big.ringedSite X))
    (RingedSite.ModuleCat.{u + 1} (Big.ringedSite Y)) _ _
    (moduleCat_hasDerivedCategory (Big.ringedSite Y))
    (bigInverseImageExact g)

/-- Derived big étale module inverse image is induced by the exact postcomposition functor. -/
theorem bigInverseImage_eq (g : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}] :
    bigInverseImage g =
      @ExactFunctor.mapDerivedCategory
        (RingedSite.ModuleCat.{u + 1} (Big.ringedSite X)) _ _
        (moduleCat_hasDerivedCategory (Big.ringedSite X))
        (RingedSite.ModuleCat.{u + 1} (Big.ringedSite Y)) _ _
        (moduleCat_hasDerivedCategory (Big.ringedSite Y))
        (bigInverseImageExact g) := rfl

end AlgebraicGeometry.AlgebraicSpace.Etale.Module.Derived

end
