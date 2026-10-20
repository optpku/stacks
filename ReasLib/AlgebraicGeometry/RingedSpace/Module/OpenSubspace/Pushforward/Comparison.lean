/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pushforward.Composition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Comparison maps for pushforward from open subspaces

This file owns the functorial comparison API for direct images from nested open subspaces.  It
also packages these comparisons after further pushforward along an arbitrary morphism of ringed
spaces.
-/

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.OpenSubspace.Pushforward

variable {X : RingedSpace.{u}}

/-- Direct image of module sheaves along the inclusion of nested open subspaces `W ⊆ U`. -/
@[stacks 08DP "pushforward between open subspaces"]
abbrev between {W U : Opens X.carrier} (h : W ≤ U) :
    openSubspaceModuleCategory X W ⥤ openSubspaceModuleCategory X U :=
  RingedSpace.Hom.pushforward (restrictedMorphismBetweenOpens X h)

/-- Restriction from `U` to `W` is left adjoint to direct image along `W ⊆ U`. -/
@[stacks 08DP "adjunction between open subspaces"]
noncomputable def betweenAdjunction {W U : Opens X.carrier} (h : W ≤ U) :
    moduleRestrictionBetweenOpens X h ⊣ between h :=
  RingedSpace.Hom.pullbackPushforwardAdjunction (restrictedMorphismBetweenOpens X h)

/-- The canonical isomorphism from iterated direct image through `U` to direct image from `W`. -/
@[stacks 08DP "composition isomorphism for pushforwards from open subspaces"]
noncomputable def compIso {W U : Opens X.carrier} (h : W ≤ U) :
    between h ⋙ modulePushforwardFromOpen U ≅ modulePushforwardFromOpen W :=
  (RingedSpace.Hom.pushforwardCompIso
      (restrictedMorphismBetweenOpens X h) (X.ofRestrict U.isOpenEmbedding)).symm ≪≫
    eqToIso (congrArg RingedSpace.Hom.pushforward
      (InducedCategory.hom_ext
        (PresheafedSpace.IsOpenImmersion.lift_fac (X.ofRestrict U.isOpenEmbedding).hom
          (X.ofRestrict W.isOpenEmbedding).hom
          (fun _ ⟨w, hw⟩ ↦ ⟨⟨w.1, h w.2⟩, hw⟩))))

/-- The comparison from direct image over `U` to direct image over `W`, applied to the
restrictions of an ambient module. -/
@[stacks 08DP "restriction map on open-subspace pushforwards"]
noncomputable def restrictionMap {W U : Opens X.carrier} (h : W ≤ U)
    (F : RingedSpace.Modules X) :
    (modulePushforwardFromOpen U).obj ((moduleRestrictionToOpen X U).obj F) ⟶
      (modulePushforwardFromOpen W).obj ((moduleRestrictionToOpen X W).obj F) :=
  (modulePushforwardFromOpen U).map
      ((betweenAdjunction h).unit.app ((moduleRestrictionToOpen X U).obj F)) ≫
    (compIso h).hom.app
      ((moduleRestrictionBetweenOpens X h).obj ((moduleRestrictionToOpen X U).obj F)) ≫
    (modulePushforwardFromOpen W).map ((OpenSubspace.Restriction.compIso X h).hom.app F)

/-- The open-subspace restriction comparison is natural in the ambient module. -/
theorem restrictionMap_naturality {W U : Opens X.carrier} (h : W ≤ U)
    {F G : RingedSpace.Modules X} (φ : F ⟶ G) :
    (moduleRestrictionToOpen X U ⋙ modulePushforwardFromOpen U).map φ ≫
        restrictionMap h G =
      restrictionMap h F ≫
        (moduleRestrictionToOpen X W ⋙ modulePushforwardFromOpen W).map φ := sorry

/-- Restrict to `U`, push forward to `X`, then push forward along `f : X ⟶ Y`. -/
@[stacks 08DP "pushforward after restriction to an open subspace"]
abbrev along {Y : RingedSpace.{u}} (f : X ⟶ Y) (U : Opens X.carrier) :
    RingedSpace.Modules X ⥤ RingedSpace.Modules Y :=
  moduleRestrictionToOpen X U ⋙ modulePushforwardFromOpen U ⋙
    RingedSpace.Hom.pushforward f

/-- Pushforward after restriction to an open subspace is additive whenever pushforward along the
ambient morphism is additive. -/
@[stacks 08DP "additivity of pushforward after open restriction"]
instance alongAdditive {Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(RingedSpace.Hom.pushforward f).Additive] (U : Opens X.carrier) :
    (along f U).Additive := sorry

/-- Naturality of the unit comparison after applying direct image along `f`. -/
theorem alongUnit_naturality {Y : RingedSpace.{u}} (f : X ⟶ Y)
    (U : Opens X.carrier) {F G : RingedSpace.Modules X} (φ : F ⟶ G) :
    (RingedSpace.Hom.pushforward f).map φ ≫
        (RingedSpace.Hom.pushforward f).map ((adjunction X U).unit.app G) =
      (RingedSpace.Hom.pushforward f).map ((adjunction X U).unit.app F) ≫
        (RingedSpace.Hom.pushforward f).map
          ((moduleRestrictionToOpen X U ⋙ modulePushforwardFromOpen U).map φ) := sorry

/-- The adjunction unit, followed by direct image along `f`, as a natural transformation. -/
@[stacks 08DP "unit after pushforward from an open subspace"]
noncomputable def alongUnit {Y : RingedSpace.{u}} (f : X ⟶ Y) (U : Opens X.carrier) :
    RingedSpace.Hom.pushforward f ⟶ along f U where
  app F := (RingedSpace.Hom.pushforward f).map ((adjunction X U).unit.app F)
  naturality {_ _} φ := alongUnit_naturality f U φ

/-- Naturality of the nested-open comparison after applying direct image along `f`. -/
theorem alongRestriction_naturality {Y : RingedSpace.{u}} (f : X ⟶ Y)
    {W U : Opens X.carrier} (h : W ≤ U) {F G : RingedSpace.Modules X} (φ : F ⟶ G) :
    (along f U).map φ ≫ (RingedSpace.Hom.pushforward f).map (restrictionMap h G) =
      (RingedSpace.Hom.pushforward f).map (restrictionMap h F) ≫ (along f W).map φ := sorry

/-- The restriction comparison for nested opens, followed by direct image along `f`, as a
natural transformation. -/
@[stacks 08DP "restriction comparison after further pushforward"]
noncomputable def alongRestriction {Y : RingedSpace.{u}} (f : X ⟶ Y)
    {W U : Opens X.carrier} (h : W ≤ U) : along f U ⟶ along f W where
  app F := (RingedSpace.Hom.pushforward f).map (restrictionMap h F)
  naturality {_ _} φ := alongRestriction_naturality f h φ

end AlgebraicGeometry.RingedSpace.OpenSubspace.Pushforward
