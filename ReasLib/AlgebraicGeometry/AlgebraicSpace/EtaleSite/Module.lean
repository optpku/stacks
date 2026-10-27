/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BigStructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ModuleComparison

/-! # Module functors on big and small étale sites of algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Restriction of global sections along pullback projections is natural in the slice object. -/
theorem bigStructureSheafMap_naturality (f : Y ⟶ X)
    {U V : (Over X)ᵒᵖ} (h : U ⟶ V) :
    (Big.structureSheaf X).obj.map h ≫ Big.gammaMap (pullback.fst V.unop.hom f) =
      Big.gammaMap (pullback.fst U.unop.hom f) ≫
        (((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
          (overEtaleTopology X) (overEtaleTopology Y)).obj
            (Big.structureSheaf Y)).obj.map h :=
  sorry

/-- The coefficient map on big étale sites induced by the pullback projections. -/
def bigStructureSheafMap (f : Y ⟶ X) :
    Big.structureSheaf X ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (overEtaleTopology X) (overEtaleTopology Y)).obj (Big.structureSheaf Y) :=
  InducedCategory.homMk
    { app := fun U => Big.gammaMap (pullback.fst U.unop.hom f)
      naturality := fun _ _ h => bigStructureSheafMap_naturality f h }

/-- The coefficient map at a slice object is restriction along its first pullback projection. -/
theorem bigStructureSheafMap_app (f : Y ⟶ X) (U : (Over X)ᵒᵖ) :
    (bigStructureSheafMap f).hom.app U =
      Big.gammaMap (pullback.fst U.unop.hom f) := rfl

/-- Identity maps on global sections are natural under postcomposition of slice objects. -/
theorem bigInverseStructureSheafMap_naturality (g : Y ⟶ X)
    {U V : (Over Y)ᵒᵖ} (h : U ⟶ V) :
    (Big.structureSheaf Y).obj.map h ≫ 𝟙 (Big.gamma V.unop.left) =
      𝟙 (Big.gamma U.unop.left) ≫
        (((Over.map g).sheafPushforwardContinuous RingCat.{u}
          (overEtaleTopology Y) (overEtaleTopology X)).obj
            (Big.structureSheaf X)).obj.map h :=
  sorry

/-- The coefficient map for postcomposition is the identity on global sections. -/
def bigInverseStructureSheafMap (g : Y ⟶ X) :
    Big.structureSheaf Y ⟶
      ((Over.map g).sheafPushforwardContinuous RingCat.{u}
        (overEtaleTopology Y) (overEtaleTopology X)).obj (Big.structureSheaf X) :=
  InducedCategory.homMk
    { app := fun U => 𝟙 (Big.gamma U.unop.left)
      naturality := fun _ _ h => bigInverseStructureSheafMap_naturality g h }

/-- Each component of the coefficient map for postcomposition is an identity. -/
theorem bigInverseStructureSheafMap_app (g : Y ⟶ X) (U : (Over Y)ᵒᵖ) :
    (bigInverseStructureSheafMap g).hom.app U = 𝟙 (Big.gamma U.unop.left) := rfl

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

namespace AlgebraicGeometry.AlgebraicSpace.Etale

/-- The geometric small étale module direct image is additive. -/
instance etaleSmallModulePushforward_additive {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [(SheafOfModules.pushforward.{u + 1} (smallChartStructureMap Y)).IsRightAdjoint] :
    (etaleSmallModulePushforward f).Additive :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Module

open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Direct image of module sheaves on big étale slice sites. -/
def bigDirectImage (f : Y ⟶ X) :
    SheafOfModules.{u + 1} (Big.structureSheaf Y) ⥤
      SheafOfModules.{u + 1} (Big.structureSheaf X) :=
  SheafOfModules.pushforward.{u + 1} (bigStructureSheafMap f)

/-- Big étale module direct image is pushforward with the pullback-projection coefficient map. -/
theorem bigDirectImage_eq (f : Y ⟶ X) :
    bigDirectImage f = SheafOfModules.pushforward.{u + 1} (bigStructureSheafMap f) := rfl

/-- Big étale module direct image is additive. -/
instance bigDirectImage_additive (f : Y ⟶ X) :
    (bigDirectImage f).Additive :=
  sorry

/-- Inverse image on big étale module sheaves induced by postcomposition. -/
def bigInverseImage (g : Y ⟶ X) :
    SheafOfModules.{u + 1} (Big.structureSheaf X) ⥤
      SheafOfModules.{u + 1} (Big.structureSheaf Y) :=
  SheafOfModules.pushforward.{u + 1} (bigInverseStructureSheafMap g)

/-- Big étale module inverse image is pushforward with identity coefficient components. -/
theorem bigInverseImage_eq (g : Y ⟶ X) :
    bigInverseImage g =
      SheafOfModules.pushforward.{u + 1} (bigInverseStructureSheafMap g) := rfl

end AlgebraicGeometry.AlgebraicSpace.Etale.Module

end
