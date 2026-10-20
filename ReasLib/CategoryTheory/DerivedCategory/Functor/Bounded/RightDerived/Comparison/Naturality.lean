/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.Naturality
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Bounded-Below Right-Derived Model Comparisons

The localization-model and canonical-single degree constructions are functors
of the chosen right-derived model. Their pointwise comparison is promoted to
a natural isomorphism between those model functors.
-/

open CategoryTheory
open scoped CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.degree.fromHomotopy

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- Evaluation through the localization-model single functor is functorial in
the chosen bounded-below right-derived model. -/
@[stacks 015A "localization-model right-derived degree functor"]
noncomputable def modelFunctor (i : ℤ) :
    (DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) ⥤ A ⥤ B :=
  ((Functor.whiskeringLeft A (DerivedCategory.Plus A)
      (DerivedCategory.Plus B)).obj
      (DerivedCategory.Plus.singleFunctor.fromHomotopy A 0)) ⋙
    ((Functor.whiskeringRight A (DerivedCategory.Plus B) B).obj
      (DerivedCategory.Plus.homologyFunctor B i))

/-- A transformation of right-derived models acts on localization-model
degree functors. -/
@[stacks 015A "naturality of localization-model right-derived degrees"]
noncomputable def map
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (τ : RF ⟶ RG) (i : ℤ) :
    (modelFunctor i).obj RF ⟶ (modelFunctor i).obj RG :=
  (modelFunctor i).map τ

/-- The component of a localization-model degree map is computed by applying
homology to the model transformation. -/
@[simp]
theorem map_app
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (τ : RF ⟶ RG) (i : ℤ) (X : A) :
    (map τ i).app X =
      (DerivedCategory.Plus.homologyFunctor B i).map
        (τ.app
          ((DerivedCategory.Plus.singleFunctor.fromHomotopy A 0).obj X)) := sorry

/-- Localization-model degree maps preserve identity transformations. -/
@[simp]
theorem map_id
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) (i : ℤ) :
    map (𝟙 RF) i = 𝟙 ((modelFunctor i).obj RF) := sorry

/-- Localization-model degree maps preserve composition. -/
@[simp]
theorem map_comp
    {RF RG RH : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (τ : RF ⟶ RG) (σ : RG ⟶ RH) (i : ℤ) :
    map (τ ≫ σ) i = map τ i ≫ map σ i := sorry

/-- An isomorphism of right-derived models acts on localization-model degree
functors. -/
@[stacks 015A "localization-model right-derived degree isomorphism"]
noncomputable def mapIso
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (e : RF ≅ RG) (i : ℤ) :
    (modelFunctor i).obj RF ≅ (modelFunctor i).obj RG :=
  (modelFunctor i).mapIso e

/-- The forward transformation of a localization-model degree isomorphism is
the induced localization-model degree map. -/
@[simp]
theorem mapIso_hom
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (e : RF ≅ RG) (i : ℤ) :
    (mapIso e i).hom = map e.hom i := sorry

/-- The inverse transformation of a localization-model degree isomorphism is
the induced localization-model degree map. -/
@[simp]
theorem mapIso_inv
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (e : RF ≅ RG) (i : ℤ) :
    (mapIso e i).inv = map e.inv i := sorry

/-- The localization-model comparison is natural in the chosen right-derived
model. -/
@[stacks 015A "natural comparison of right-derived degree models"]
noncomputable def iso (i : ℤ) :
    modelFunctor (A := A) (B := B) i ≅
      RightDerived.degree.modelFunctor i where
  hom :=
    { app := fun RF ↦ (RightDerived.degree.fromHomotopyIso RF i).hom
      naturality := sorry }
  inv :=
    { app := fun RF ↦ (RightDerived.degree.fromHomotopyIso RF i).inv
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The component of the natural model comparison is the original pointwise
comparison isomorphism. -/
@[simp]
theorem iso_app
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) (i : ℤ) :
    (iso (A := A) (B := B) i).app RF =
      RightDerived.degree.fromHomotopyIso RF i := sorry

namespace iso

/-- The forward model comparison commutes with transformations of
right-derived models. -/
@[reassoc, stacks 015A "naturality of the right-derived model comparison"]
theorem hom_naturality
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (τ : RF ⟶ RG) (i : ℤ) :
    map τ i ≫ (RightDerived.degree.fromHomotopyIso RG i).hom =
      (RightDerived.degree.fromHomotopyIso RF i).hom ≫
        RightDerived.degree.map τ i := sorry

/-- The inverse model comparison commutes with transformations of
right-derived models. -/
@[reassoc, stacks 015A "naturality of the inverse right-derived model comparison"]
theorem inv_naturality
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (τ : RF ⟶ RG) (i : ℤ) :
    RightDerived.degree.map τ i ≫
        (RightDerived.degree.fromHomotopyIso RG i).inv =
      (RightDerived.degree.fromHomotopyIso RF i).inv ≫ map τ i := sorry

/-- Componentwise forward naturality of the right-derived model comparison. -/
@[reassoc (attr := simp)]
theorem hom_naturality_app
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (τ : RF ⟶ RG) (i : ℤ) (X : A) :
    (map τ i).app X ≫
        (RightDerived.degree.fromHomotopyIso RG i).hom.app X =
      (RightDerived.degree.fromHomotopyIso RF i).hom.app X ≫
        (RightDerived.degree.map τ i).app X := sorry

/-- Componentwise inverse naturality of the right-derived model comparison. -/
@[reassoc (attr := simp)]
theorem inv_naturality_app
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (τ : RF ⟶ RG) (i : ℤ) (X : A) :
    (RightDerived.degree.map τ i).app X ≫
        (RightDerived.degree.fromHomotopyIso RG i).inv.app X =
      (RightDerived.degree.fromHomotopyIso RF i).inv.app X ≫
        (map τ i).app X := sorry

end iso

end CategoryTheory.Functor.RightDerived.degree.fromHomotopy
