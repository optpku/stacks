/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived

public section

open CategoryTheory CategoryTheory.Limits

universe u v w z

noncomputable section

namespace SheafOfModules.BaseSections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}} {A : Type w} [Ring A]
variable [UnivLE.{u, w}] (α : A →+* (limit R.obj : RingCat.{w}))

/-- Restriction to a constant base-ring action preserves the identity restriction map. -/
private theorem diagram_map_id (M : SheafOfModules.{z} R) (X : Cᵒᵖ) :
    let sections := (PresheafOfModules.restrictScalars
      ((Functor.const Cᵒᵖ).map (RingCat.ofHom α) ≫ (limit.cone R.obj).π)).obj M.val
    sections.map (𝟙 X) = 𝟙 (sections.obj X) := sorry

/-- Restriction to a constant base-ring action preserves composition of restriction maps. -/
private theorem diagram_map_comp (M : SheafOfModules.{z} R)
    {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    let sections := (PresheafOfModules.restrictScalars
      ((Functor.const Cᵒᵖ).map (RingCat.ofHom α) ≫ (limit.cone R.obj).π)).obj M.val
    sections.map (f ≫ g) = sections.map f ≫ sections.map g := sorry

/-- Local sections of a module sheaf form a diagram of modules over a specified base ring. -/
def diagram (M : SheafOfModules.{z} R) : Cᵒᵖ ⥤ ModuleCat.{z} A :=
  let sections := (PresheafOfModules.restrictScalars
    ((Functor.const Cᵒᵖ).map (RingCat.ofHom α) ≫ (limit.cone R.obj).π)).obj M.val
  { obj := sections.obj
    map := sections.map
    map_id := diagram_map_id α M
    map_comp := diagram_map_comp α M }

/-- A module-sheaf morphism commutes with the base-linear restriction maps. -/
private theorem diagramMap_naturality {M N : SheafOfModules.{z} R} (φ : M ⟶ N)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (diagram α M).map f ≫ (ModuleCat.restrictScalars
        (((Functor.const Cᵒᵖ).map (RingCat.ofHom α) ≫ (limit.cone R.obj).π).app Y).hom).map
          (φ.val.app Y) =
      (ModuleCat.restrictScalars
        (((Functor.const Cᵒᵖ).map (RingCat.ofHom α) ≫ (limit.cone R.obj).π).app X).hom).map
          (φ.val.app X) ≫ (diagram α N).map f := sorry

/-- A morphism of module sheaves induces the actual component maps on base-linear sections. -/
def diagramMap {M N : SheafOfModules.{z} R} (φ : M ⟶ N) :
    diagram α M ⟶ diagram α N where
  app X := (ModuleCat.restrictScalars
    (((Functor.const Cᵒᵖ).map (RingCat.ofHom α) ≫ (limit.cone R.obj).π).app X).hom).map
      (φ.val.app X)
  naturality {_ _} f := diagramMap_naturality α φ f

/-- The componentwise map of base-linear diagrams preserves identity morphisms. -/
private theorem diagramFunctor_map_id (M : SheafOfModules.{z} R) :
    diagramMap α (𝟙 M) = 𝟙 (diagram α M) := sorry

/-- The componentwise map of base-linear diagrams preserves composition. -/
private theorem diagramFunctor_map_comp {M N P : SheafOfModules.{z} R}
    (φ : M ⟶ N) (ψ : N ⟶ P) :
    diagramMap α (φ ≫ ψ) = diagramMap α φ ≫ diagramMap α ψ := sorry

/-- Taking local sections with a fixed base action is functorial in the module sheaf. -/
def diagramFunctor : SheafOfModules.{z} R ⥤ Cᵒᵖ ⥤ ModuleCat.{z} A where
  obj := diagram α
  map := diagramMap α
  map_id := diagramFunctor_map_id α
  map_comp := diagramFunctor_map_comp α

variable [UnivLE.{u, z}]

/-- Global sections with a specified base action are the limit of local sections. -/
def globalSections : SheafOfModules.{z} R ⥤ ModuleCat.{z} A :=
  diagramFunctor.{u, v, w, z} α ⋙ @lim _ _ _ _
    (ModuleCat.hasLimitsOfShape (R := A) : HasLimitsOfShape Cᵒᵖ (ModuleCat.{z} A))

/-- Global sections with a specified base action form an additive functor. -/
instance globalSections_additive :
    (globalSections.{u, v, w, z} α).Additive := sorry

variable [HasSheafify J AddCommGrpCat.{z}] [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable [IsGrothendieckAbelian.{z} (SheafOfModules.{z} R)]
variable [HasDerivedCategory.{max (max (max u v) w) (z + 1)} (SheafOfModules.{z} R)]

/-- The canonical total right derived functor computes base-linear derived global sections. -/
def derivedGlobalSections :
    DerivedCategory (SheafOfModules.{z} R) ⥤ DerivedCategory (ModuleCat.{z} A) :=
  Functor.RightDerived.KInjective.functor (globalSections.{u, v, w, z} α)

/-- An ordinary morphism of module sheaves induces a base-linear arrow on derived sections. -/
def map {M N : SheafOfModules.{z} R} (φ : M ⟶ N) :
    (derivedGlobalSections α).obj ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj M) ⟶
      (derivedGlobalSections α).obj ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj N) :=
  (derivedGlobalSections α).map ((DerivedCategory.singleFunctor _ (0 : ℤ)).map φ)

end SheafOfModules.BaseSections
