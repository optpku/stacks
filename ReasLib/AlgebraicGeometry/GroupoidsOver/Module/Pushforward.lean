/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.LowerShriek

/-!
# Module pushforward on associated sites

Pushforward is computed by compatible families over structured arrows. Higher
direct images are the right derived functors of this module-sheaf functor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

namespace ModulePushforward

/-- The diagram of module sections over arrows from a target object, with scalars
restricted along the structure-sheaf comparison and the structural arrow. -/
def diagram (f : X ⟶ Y) (τ : StandardTopology)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (y : Y.totalᵒᵖ) :
    StructuredArrow y (toFunctor f).op ⥤
      ModuleCat.{u + 1} ((associatedStructureSheaf Y τ).obj.obj y) :=
  let component := fun a : StructuredArrow y (toFunctor f).op ↦
    (ModuleCat.restrictScalars
      (((associatedStructureSheafInverseImageIso f τ).hom.hom.app a.right).hom.comp
        ((associatedStructureSheaf Y τ).obj.map a.hom).hom)).obj (F.val.obj a.right)
  { obj := component
    map := fun {a b} k ↦ ModuleCat.ofHom (X := component a) (Y := component b)
      { toFun := fun s ↦ F.val.map k.right s
        map_add' := sorry
        map_smul' := sorry }
    map_id := sorry
    map_comp := sorry }

/-- Compatible sections over all structured arrows out of a target object form a
module over the structure ring at that object. -/
def sections (f : X ⟶ Y) (τ : StandardTopology)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (y : Y.totalᵒᵖ) :
    ModuleCat.{u + 1} ((associatedStructureSheaf Y τ).obj.obj y) :=
  ModuleCat.of _ (ModuleCat.sectionsSubmodule (diagram f τ F y))

end ModulePushforward

/-- Pushforward of module sheaves, computed by compatible families over structured
arrows, with restrictions given by precomposition of their structural arrows. -/
def associatedModulePushforward (f : X ⟶ Y) (τ : StandardTopology) :
    SheafOfModules.{u + 1} (associatedStructureSheaf X τ) ⥤
      SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) where
  obj F :=
    { val :=
        { obj := ModulePushforward.sections f τ F
          map := fun {y z} h ↦ ModuleCat.ofHom
            (X := ModulePushforward.sections f τ F y)
            (Y := (ModuleCat.restrictScalars ((associatedStructureSheaf Y τ).obj.map h).hom).obj
              (ModulePushforward.sections f τ F z))
            { toFun := fun s ↦ ⟨fun a ↦ s.val (StructuredArrow.mk (h ≫ a.hom)), sorry⟩
              map_add' := sorry
              map_smul' := sorry }
          map_id := sorry
          map_comp := sorry }
      isSheaf := sorry }
  map {F G} φ :=
    { val :=
        { app := fun y ↦ ModuleCat.ofHom
            (X := ModulePushforward.sections f τ F y) (Y := ModulePushforward.sections f τ G y)
            { toFun := fun s ↦ ⟨fun a ↦ φ.val.app a.right (s.val a), sorry⟩
              map_add' := sorry
              map_smul' := sorry }
          naturality := sorry } }
  map_id := sorry
  map_comp := sorry

/-- Evaluating module pushforward gives the compatible-section module. -/
theorem associatedModulePushforward_obj (f : X ⟶ Y) (τ : StandardTopology)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (y : Y.totalᵒᵖ) :
    ((associatedModulePushforward f τ).obj F).val.obj y =
      ModulePushforward.sections f τ F y := sorry

/-- Pushforward applies a module-sheaf morphism to each component of a compatible family. -/
theorem associatedModulePushforward_map_apply (f : X ⟶ Y) (τ : StandardTopology)
    {F G : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)} (φ : F ⟶ G)
    (y : Y.totalᵒᵖ) (s : ModulePushforward.sections f τ F y)
    (a : StructuredArrow y (toFunctor f).op) :
    ((((associatedModulePushforward f τ).map φ).val.app y s).val a) =
      φ.val.app a.right (s.val a) := sorry

/-- Restriction of pushforward sections precomposes the structural arrow of each
component with the target restriction arrow. -/
theorem associatedModulePushforward_restriction_apply (f : X ⟶ Y) (τ : StandardTopology)
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
    {y z : Y.totalᵒᵖ} (h : y ⟶ z) (s : ModulePushforward.sections f τ F y)
    (a : StructuredArrow z (toFunctor f).op) :
    ((((associatedModulePushforward f τ).obj F).val.map h s).val a) =
      s.val (StructuredArrow.mk (h ≫ a.hom)) := sorry

/-- Module pushforward on associated sites is additive. -/
instance associatedModulePushforward_additive (f : X ⟶ Y) (τ : StandardTopology) :
    (associatedModulePushforward f τ).Additive := sorry

variable (f : X ⟶ Y) (τ : StandardTopology)
variable [HasInjectiveResolutions
    (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))]

/-- The degree-`i` higher direct image functor `R^i f_*` on sheaves of modules. -/
abbrev associatedModuleHigherDirectImageFunctor (i : ℕ) :
    SheafOfModules.{u + 1} (associatedStructureSheaf X τ) ⥤
      SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) :=
  (associatedModulePushforward f τ).rightDerived i

/-- The degree-`i` higher direct image `R^i f_* F` of a sheaf of modules. -/
abbrev associatedModuleHigherDirectImage
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (i : ℕ) :
    SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) :=
  (associatedModuleHigherDirectImageFunctor f τ i).obj F

/-- `associatedModuleHigherDirectImage f τ F i` is the object map of `rightDerived`
of module pushforward. -/
theorem associatedModuleHigherDirectImage_eq
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (i : ℕ) :
    associatedModuleHigherDirectImage f τ F i =
      ((associatedModulePushforward f τ).rightDerived i).obj F :=
  rfl

end AlgebraicGeometry.GroupoidsOver
