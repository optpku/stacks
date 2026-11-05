/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module-valued global sections on ringed sites

This module constructs the global-sections ring of an arbitrary ringed site and the corresponding
module-valued global-sections functor.  Derived global sections are kept in the sibling
`Derived` module.
-/

@[expose] public section

-- Exposed concrete functors use private Prop-valued law certificates.
set_option backward.privateInPublic true

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe z u v w

namespace RingedSite.Hom

/-- The ring `Γ(𝒞, 𝒪_X)` of global sections of the structure sheaf of a ringed site. -/
@[stacks 0D6H "global-sections ring"]
abbrev globalSectionsRing (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] : RingCat.{w} :=
  limit X.structureSheaf.obj

/-- The constant presheaf on the global-sections ring of a ringed site. -/
abbrev globalSectionsRingPresheaf (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] :
    X.carrierᵒᵖ ⥤ RingCat.{w} :=
  (Functor.const X.carrierᵒᵖ).obj (globalSectionsRing X)

/-- Evaluation of a global section gives a morphism from the constant global-sections presheaf
to the structure sheaf. -/
abbrev globalSectionsRingHom (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] :
    globalSectionsRingPresheaf X ⟶ X.structureSheaf.obj :=
  (limit.cone X.structureSheaf.obj).π

/-- Restricting scalars along `globalSectionsRingHom` turns module sheaves into presheaves of
modules over the constant global-sections ring. -/
abbrev moduleGlobalSectionsPresheaf (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] :
    ModuleCat.{z} X ⥤ PresheafOfModules.{z} (globalSectionsRingPresheaf X) :=
  SheafOfModules.forget X.structureSheaf ⋙
    PresheafOfModules.restrictScalars (globalSectionsRingHom X)

/-- Identity restriction acts as the identity on sections over the global-sections ring. -/
private theorem moduleGlobalSectionsDiagram_map_id
    (X : RingedSite.{u, v, w}) [UnivLE.{u, w}]
    (ℱ : ModuleCat.{z} X) (U : X.carrierᵒᵖ) :
    ((moduleGlobalSectionsPresheaf X).obj ℱ).map (𝟙 U) =
      𝟙 (((moduleGlobalSectionsPresheaf X).obj ℱ).obj U) := by
  ext x
  simp
  rfl

/-- Restriction of sections over the global-sections ring respects composition. -/
private theorem moduleGlobalSectionsDiagram_map_comp
    (X : RingedSite.{u, v, w}) [UnivLE.{u, w}]
    (ℱ : ModuleCat.{z} X) {U V W : X.carrierᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    ((moduleGlobalSectionsPresheaf X).obj ℱ).map (f ≫ g) =
      ((moduleGlobalSectionsPresheaf X).obj ℱ).map f ≫
        ((moduleGlobalSectionsPresheaf X).obj ℱ).map g := by
  ext x
  exact PresheafOfModules.map_comp_apply _ f g x

/-- The diagram of local sections of a module sheaf, regarded as modules over the global-sections
ring. -/
abbrev moduleGlobalSectionsDiagram (X : RingedSite.{u, v, w}) [UnivLE.{u, w}]
    (ℱ : ModuleCat.{z} X) :
    X.carrierᵒᵖ ⥤ _root_.ModuleCat.{z} (globalSectionsRing X) where
  obj := fun U ↦ ((moduleGlobalSectionsPresheaf X).obj ℱ).obj U
  map := fun f ↦ ((moduleGlobalSectionsPresheaf X).obj ℱ).map f
  map_id := moduleGlobalSectionsDiagram_map_id X ℱ
  map_comp := moduleGlobalSectionsDiagram_map_comp X ℱ

/-- Morphisms of module sheaves commute with restriction over the global-sections ring. -/
private theorem moduleGlobalSectionsDiagramMap_naturality
    (X : RingedSite.{u, v, w}) [UnivLE.{u, w}]
    {ℱ 𝒢 : ModuleCat.{z} X} (f : ℱ ⟶ 𝒢) {U V : X.carrierᵒᵖ} (g : U ⟶ V) :
    (moduleGlobalSectionsDiagram X ℱ).map g ≫
        ((moduleGlobalSectionsPresheaf X).map f).app V =
      ((moduleGlobalSectionsPresheaf X).map f).app U ≫
        (moduleGlobalSectionsDiagram X 𝒢).map g := by
  ext x
  exact PresheafOfModules.naturality_apply _ g x

/-- A morphism of module sheaves induces the objectwise morphism between their diagrams of
sections over the global-sections ring. -/
noncomputable def moduleGlobalSectionsDiagramMap
    (X : RingedSite.{u, v, w}) [UnivLE.{u, w}]
    {ℱ 𝒢 : ModuleCat.{z} X} (f : ℱ ⟶ 𝒢) :
    moduleGlobalSectionsDiagram X ℱ ⟶ moduleGlobalSectionsDiagram X 𝒢 where
  app U := ((moduleGlobalSectionsPresheaf X).map f).app U
  naturality {_ _} g := moduleGlobalSectionsDiagramMap_naturality X f g

/-- The identity module-sheaf morphism induces the identity section-diagram morphism. -/
private theorem moduleGlobalSectionsDiagramFunctor_map_id
    (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] (ℱ : ModuleCat.{z} X) :
    moduleGlobalSectionsDiagramMap X (𝟙 ℱ) = 𝟙 (moduleGlobalSectionsDiagram X ℱ) := by
  ext U x
  rfl

/-- The section-diagram morphism of a composite is the composite of section-diagram morphisms. -/
private theorem moduleGlobalSectionsDiagramFunctor_map_comp
    (X : RingedSite.{u, v, w}) [UnivLE.{u, w}]
    {ℱ 𝒢 ℋ : ModuleCat.{z} X} (f : ℱ ⟶ 𝒢) (g : 𝒢 ⟶ ℋ) :
    moduleGlobalSectionsDiagramMap X (f ≫ g) =
      moduleGlobalSectionsDiagramMap X f ≫ moduleGlobalSectionsDiagramMap X g := by
  ext U x
  rfl

/-- Module sheaves map functorially to their diagrams of local sections over the global-sections
ring. -/
noncomputable def moduleGlobalSectionsDiagramFunctor
    (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] :
    ModuleCat.{z} X ⥤ X.carrierᵒᵖ ⥤ _root_.ModuleCat.{z} (globalSectionsRing X) where
  obj := moduleGlobalSectionsDiagram X
  map := moduleGlobalSectionsDiagramMap X
  map_id := moduleGlobalSectionsDiagramFunctor_map_id X
  map_comp := moduleGlobalSectionsDiagramFunctor_map_comp X

/-- The category of modules over the global-sections ring has limits indexed by the site whenever
the module universe contains the site-object universe. -/
theorem moduleGlobalSectionsHasLimitsOfShape
    (X : RingedSite.{u, v, w}) [UnivLE.{u, w}] [UnivLE.{u, z}] :
    HasLimitsOfShape X.carrierᵒᵖ (_root_.ModuleCat.{z} (globalSectionsRing X)) :=
  _root_.ModuleCat.hasLimitsOfShape

/-- The module of compatible global sections of a module sheaf on a ringed site. -/
abbrev moduleGlobalSectionsObject (X : RingedSite.{u, v, w})
    [UnivLE.{u, w}] [UnivLE.{u, z}] (ℱ : ModuleCat.{z} X) :
    _root_.ModuleCat.{z} (globalSectionsRing X) :=
  @limit _ _ _ _ (moduleGlobalSectionsDiagram X ℱ)
    (@HasLimitsOfShape.has_limit _ _ _ _
      (moduleGlobalSectionsHasLimitsOfShape X) (moduleGlobalSectionsDiagram X ℱ))

/-- The `Γ(𝒞, 𝒪_X)`-module-valued global-sections functor on `𝒪_X`-modules. -/
@[stacks 0D6H "module-valued global sections"]
abbrev moduleGlobalSectionsFunctor (X : RingedSite.{u, v, w})
    [UnivLE.{u, w}] [UnivLE.{u, z}] :
    ModuleCat.{z} X ⥤ _root_.ModuleCat.{z} (globalSectionsRing X) :=
  moduleGlobalSectionsDiagramFunctor X ⋙
    @lim _ _ _ _ (moduleGlobalSectionsHasLimitsOfShape X)

/-- The additive global-sections functor on `𝒪_X`-modules, computed after forgetting to
abelian sheaves. -/
@[stacks 0D6H "additive global sections"]
abbrev moduleGlobalSectionsAdditiveFunctor (X : RingedSite.{u, v, w})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}] :
    ModuleCat.{z} X ⥤ AddCommGrpCat.{z} :=
  SheafOfModules.toSheaf.{z} X.structureSheaf ⋙
    Sheaf.Γ X.siteTopology AddCommGrpCat.{z}

/-- Forgetting the `Γ(𝒞, 𝒪_X)`-module structure on global sections recovers the additive
global-sections functor. -/
theorem moduleGlobalSectionsForget_eq (X : RingedSite.{u, v, w})
    [UnivLE.{u, w}] [UnivLE.{u, z}]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}] :
    moduleGlobalSectionsFunctor.{z} X ⋙
        forget₂ (_root_.ModuleCat.{z} (globalSectionsRing X)) AddCommGrpCat.{z} =
      moduleGlobalSectionsAdditiveFunctor.{z} X := sorry

end RingedSite.Hom
