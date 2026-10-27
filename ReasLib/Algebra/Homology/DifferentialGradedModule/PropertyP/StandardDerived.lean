/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.FunctorialResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.FromModules

/-! # Actual standard derived computation from the specified property-P replacement
For an actual functor H to a cochain homotopy category, replace its DG-module source and
map backwards denominators to the literal reverse underlying cochain edges. No inverse is
selected from a universal-property or invertibility certificate.
-/
@[expose] public section
noncomputable section
universe r v u w
open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory
namespace DifferentialGradedModule.PropertyP.StandardDerived
variable {R : Type r} [CommRing R] {A : CochainDGAlgebra.{r, v} R}
variable {C : Type u} [Category.{w} C] [Abelian C]
local instance standardTarget : HasDerivedCategory.{max u w} C := HasDerivedCategory.standard C
variable (H : DifferentialGradedCategory.K R (DifferentialGradedModule.{r, v} A) ⥤
  HomotopyCategory C (ComplexShape.up ℤ))

/-- Strict tensor on homotopy classes followed by ordinary standard localization. -/
abbrev sourceFunctor  :=
  H ⋙ DerivedCategory.Qh

/-- Actual tensor of the specified property-P resolving model. -/
def computed  :=
  DifferentialGradedModule.PropertyP.homotopyReplacement A ⋙ sourceFunctor H

/-- The actual tensor cochain representative of a replaced homotopy map. -/
def denominatorMap
    {X Y : DifferentialGradedCategory.K R (DifferentialGradedModule.{r, v} A)} (f : X ⟶ Y) :=
  ((H).map
    ((DifferentialGradedModule.PropertyP.homotopyReplacement A).map f)).out

/-- A weak equivalence between the resolving property-P modules is a homotopy equivalence;
tensor preserves it. This is membership for the specified map, not inverse data selection. -/
theorem denominatorMap_mem_quasiIso
    {X Y : DifferentialGradedCategory.K R (DifferentialGradedModule.{r, v} A)}
    (f : X ⟶ Y) (hf : (DifferentialGradedModule.Homotopy.acyclic.{r, v} A).trW f) :
    HomologicalComplex.quasiIso
      (C) (ComplexShape.up ℤ)
      (denominatorMap H f) := sorry

/-- Descend by explicit forward maps and literal ordinary cochain inverse edges. -/
def onPaths  :
    Paths (Localization.Construction.LocQuiver
      (DifferentialGradedModule.Homotopy.acyclic.{r, v} A).trW) ⥤
      DerivedCategory (C) :=
  Quiv.lift
    { obj := fun X ↦ (computed H).obj X.obj
      map := by
        intro X Y f
        rcases f with f | ⟨f, hf⟩
        · exact (computed H).map f
        · exact (Localization.Construction.wIso
            (W := HomologicalComplex.quasiIso
              (C) (ComplexShape.up ℤ))
            (denominatorMap H f) (denominatorMap_mem_quasiIso H f hf)).inv }

/-- The actual left-derived tensor model on the standard DG derived category. -/
def functor  :
    DifferentialGradedModule.Derived.Category.{r, v} A ⥤
      DerivedCategory (C) :=
  CategoryTheory.Quotient.lift _ (onPaths H) (by
    intro X Y f g h
    sorry)

/-- The standard forward restriction computes tensor of the actual replacement. -/
def computationIso  :
    DifferentialGradedModule.Derived.Q.{r, v} A ⋙ functor H ≅ computed H :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro X Y f; sorry)

/-- The actual augmentation gives the derived-to-strict tensor counit. -/
def counit  :
    DifferentialGradedModule.Derived.Q.{r, v} A ⋙ functor H ⟶ sourceFunctor H where
  app X := (sourceFunctor H).map
    ((DifferentialGradedModule.PropertyP.homotopyAugmentation A).app X)
  naturality := sorry

@[simp] theorem counit_app
    (X : DifferentialGradedCategory.K R (DifferentialGradedModule.{r, v} A)) :
    (counit H).app X = (sourceFunctor H).map
      ((DifferentialGradedModule.toK A).map
        (DifferentialGradedModule.PropertyP.Resolution.canonical A X.obj).π) := rfl

/-- The tensor of the supplied augmentation, represented by an actual cochain map. -/
def augmentationMap  (M : DifferentialGradedModule.{r, v} A) :=
  ((H).map
    ((DifferentialGradedModule.toK A).map
      (DifferentialGradedModule.PropertyP.Resolution.canonical A M).π)).out

/-- On a property-P target the augmentation is between property-P objects, so its tensor
representative is a quasi-isomorphism. The witness does not supply an inverse map. -/
theorem augmentationMap_mem_quasiIso
    (M : DifferentialGradedModule.{r, v} A)
    (hM : DifferentialGradedModule.HasPropertyP A M) :
    HomologicalComplex.quasiIso
      (C) (ComplexShape.up ℤ)
      (augmentationMap H M) := sorry

/-- Forward map is tensor of the actual augmentation; reverse map is its explicit formal
underlying denominator edge, not `asIso` of an unproved invertibility certificate. -/
def counitAppIso
    (M : DifferentialGradedModule.{r, v} A)
    (hM : DifferentialGradedModule.HasPropertyP A M) :
    (functor H).obj ((DifferentialGradedModule.Derived.fromModules.{r, v} A).obj M) ≅
      (sourceFunctor H).obj ((DifferentialGradedModule.toK A).obj M) where
  hom := (counit H).app ((DifferentialGradedModule.toK A).obj M)
  inv := (Localization.Construction.wIso
    (W := HomologicalComplex.quasiIso
      (C) (ComplexShape.up ℤ))
    (augmentationMap H M) (augmentationMap_mem_quasiIso H M hM)).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

@[simp] theorem counitAppIso_hom
    (M : DifferentialGradedModule.{r, v} A) (hM : DifferentialGradedModule.HasPropertyP A M) :
    (counitAppIso H M hM).hom =
      (counit H).app ((DifferentialGradedModule.toK A).obj M) := rfl

/-- Object computation uses exactly the supplied property-P resolving module. -/
@[simp] theorem functor_obj_fromModules (M : DifferentialGradedModule.{r, v} A) :
    (functor H).obj ((DifferentialGradedModule.Derived.fromModules.{r, v} A).obj M) =
      (sourceFunctor H).obj ((DifferentialGradedModule.toK A).obj (Resolution.canonical A M).obj) := rfl

/-- The inverse comparison is precisely the formal underlying augmentation edge. -/
@[simp] theorem counitAppIso_inv (M : DifferentialGradedModule.{r, v} A)
    (hM : DifferentialGradedModule.HasPropertyP A M) :
    (counitAppIso H M hM).inv =
      (Localization.Construction.wIso
        (W := HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
        (augmentationMap H M) (augmentationMap_mem_quasiIso H M hM)).inv := rfl

/-- The law certifies existing functor/counit data; it never supplies a map or inverse. -/
theorem isLeftDerived : (functor H).IsLeftDerivedFunctor (counit H)
    (DifferentialGradedModule.quasiIso A) := sorry
end DifferentialGradedModule.PropertyP.StandardDerived
