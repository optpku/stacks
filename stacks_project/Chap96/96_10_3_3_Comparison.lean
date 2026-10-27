/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.SpaceComparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Sheafification
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StructureSheaf

/-! # Algebraic-space comparison of étale modules -/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids
open RingedSite.Hom
open scoped Bicategory

universe u

/-- Composition with the forgetful functor from rings to types preserves étale sheaves. -/
abbrev AlgebraicGeometry.GroupoidsOver.etaleTopology_hasSheafCompose
    {S : Scheme.{u}} (X : GroupoidsOver S) :
    X.etaleTopology.HasSheafCompose (forget RingCat.{u}) :=
  etaleTopology_hasSheafCompose_ring_type X

#check (AlgebraicGeometry.GroupoidsOver.etaleModuleInverseImage_comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (h : X ⟶ Y) (k : Y ⟶ Z),
    etaleModuleInverseImage k ⋙ etaleModuleInverseImage h ≅
      etaleModuleInverseImage (h ≫ k))

#check (AlgebraicGeometry.GroupoidsOver.etaleModuleInverseImage_iso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} {h₁ h₂ : X ⟶ Y} (e : h₁ ≅ h₂),
    etaleModuleInverseImage h₁ ≅ etaleModuleInverseImage h₂)

#check (AlgebraicGeometry.GroupoidsOver.etaleModuleInverseImage_twoCell :
  ∀ {S : Scheme.{u}} {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f),
    etaleModuleInverseImage g ⋙ etaleModuleInverseImage a ≅
      etaleModuleInverseImage f)

#check (AlgebraicGeometry.GroupoidsOver.restrictPullbackComparison :
  ∀ {S : Scheme.{u}} {Ucfg Vcfg : GroupoidsOver S} (a : Ucfg ⟶ Vcfg)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (G : SheafOfModules.{u} (etaleRingedSite Vcfg).structureSheaf),
    (AlgebraicSpace.Modules.pullback (moduleComparisonSpaceMorphism a eU eV)).obj
        ((restrictModules eV).obj G) ⟶
      (restrictModules eU).obj ((etaleModuleInverseImage a).obj G))

#check (AlgebraicGeometry.GroupoidsOver.moduleComparisonSpace :
  ∀ {S : Scheme.{u}} {X Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) (f : Ucfg ⟶ X) (g : Vcfg ⟶ X) (φ : a ≫ g ≅ f)
    {U V : AlgebraicSpace S} (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf),
    (AlgebraicSpace.Modules.pullback (moduleComparisonSpaceMorphism a eU eV)).obj
        ((restrictModules eV).obj ((etaleModuleInverseImage g).obj F)) ⟶
      (restrictModules eU).obj ((etaleModuleInverseImage f).obj F))
