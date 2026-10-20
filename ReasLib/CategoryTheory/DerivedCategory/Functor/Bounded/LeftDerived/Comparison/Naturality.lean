/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Degree.Naturality
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Bounded-Above Left-Derived Model Comparisons

The localization-model and canonical-single degree constructions are functors
of the chosen left-derived model. Their pointwise comparison is promoted to a
natural isomorphism between those model functors.
-/

open CategoryTheory
open scoped CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftDerived.degree.fromHomotopy

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- Evaluation through the localization-model single functor is functorial in
the chosen bounded-above left-derived model. -/
@[stacks 015A "localization-model left-derived degree functor"]
noncomputable def modelFunctor (i : ℤ) :
    (DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) ⥤ A ⥤ B :=
  ((Functor.whiskeringLeft A (DerivedCategory.Minus A)
      (DerivedCategory.Minus B)).obj
      (DerivedCategory.Minus.singleFunctor.fromHomotopy A 0)) ⋙
    ((Functor.whiskeringRight A (DerivedCategory.Minus B) B).obj
      (DerivedCategory.Minus.homologyFunctor B i))

/-- A transformation of left-derived models acts on localization-model degree
functors. -/
@[stacks 015A "naturality of localization-model left-derived degrees"]
noncomputable def map
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (i : ℤ) :
    (modelFunctor i).obj LF ⟶ (modelFunctor i).obj LG :=
  (modelFunctor i).map τ

/-- The component of a localization-model degree map is computed by applying
homology to the model transformation. -/
@[simp]
theorem map_app
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (i : ℤ) (X : A) :
    (map τ i).app X =
      (DerivedCategory.Minus.homologyFunctor B i).map
        (τ.app
          ((DerivedCategory.Minus.singleFunctor.fromHomotopy A 0).obj X)) := sorry

/-- Localization-model degree maps preserve identity transformations. -/
@[simp]
theorem map_id
    (LF : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) (i : ℤ) :
    map (𝟙 LF) i = 𝟙 ((modelFunctor i).obj LF) := sorry

/-- Localization-model degree maps preserve composition. -/
@[simp]
theorem map_comp
    {LF LG LH : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (σ : LG ⟶ LH) (i : ℤ) :
    map (τ ≫ σ) i = map τ i ≫ map σ i := sorry

/-- An isomorphism of left-derived models acts on localization-model degree
functors. -/
@[stacks 015A "localization-model left-derived degree isomorphism"]
noncomputable def mapIso
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (e : LF ≅ LG) (i : ℤ) :
    (modelFunctor i).obj LF ≅ (modelFunctor i).obj LG :=
  (modelFunctor i).mapIso e

/-- The forward transformation of a localization-model degree isomorphism is
the induced localization-model degree map. -/
@[simp]
theorem mapIso_hom
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (e : LF ≅ LG) (i : ℤ) :
    (mapIso e i).hom = map e.hom i := sorry

/-- The inverse transformation of a localization-model degree isomorphism is
the induced localization-model degree map. -/
@[simp]
theorem mapIso_inv
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (e : LF ≅ LG) (i : ℤ) :
    (mapIso e i).inv = map e.inv i := sorry

/-- The localization-model comparison is natural in the chosen left-derived
model. -/
@[stacks 015A "natural comparison of left-derived degree models"]
noncomputable def iso (i : ℤ) :
    modelFunctor (A := A) (B := B) i ≅
      LeftDerived.degree.modelFunctor i where
  hom :=
    { app := fun LF ↦ (LeftDerived.degree.fromHomotopyIso LF i).hom
      naturality := sorry }
  inv :=
    { app := fun LF ↦ (LeftDerived.degree.fromHomotopyIso LF i).inv
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The component of the natural model comparison is the original pointwise
comparison isomorphism. -/
@[simp]
theorem iso_app
    (LF : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) (i : ℤ) :
    (iso (A := A) (B := B) i).app LF =
      LeftDerived.degree.fromHomotopyIso LF i := sorry

namespace iso

/-- The forward model comparison commutes with transformations of left-derived
models. -/
@[reassoc, stacks 015A "naturality of the left-derived model comparison"]
theorem hom_naturality
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (i : ℤ) :
    map τ i ≫ (LeftDerived.degree.fromHomotopyIso LG i).hom =
      (LeftDerived.degree.fromHomotopyIso LF i).hom ≫
        LeftDerived.degree.map τ i := sorry

/-- The inverse model comparison commutes with transformations of left-derived
models. -/
@[reassoc, stacks 015A "naturality of the inverse left-derived model comparison"]
theorem inv_naturality
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (i : ℤ) :
    LeftDerived.degree.map τ i ≫
        (LeftDerived.degree.fromHomotopyIso LG i).inv =
      (LeftDerived.degree.fromHomotopyIso LF i).inv ≫ map τ i := sorry

/-- Componentwise forward naturality of the left-derived model comparison. -/
@[reassoc (attr := simp)]
theorem hom_naturality_app
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (i : ℤ) (X : A) :
    (map τ i).app X ≫
        (LeftDerived.degree.fromHomotopyIso LG i).hom.app X =
      (LeftDerived.degree.fromHomotopyIso LF i).hom.app X ≫
        (LeftDerived.degree.map τ i).app X := sorry

/-- Componentwise inverse naturality of the left-derived model comparison. -/
@[reassoc (attr := simp)]
theorem inv_naturality_app
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (i : ℤ) (X : A) :
    (LeftDerived.degree.map τ i).app X ≫
        (LeftDerived.degree.fromHomotopyIso LG i).inv.app X =
      (LeftDerived.degree.fromHomotopyIso LF i).inv.app X ≫
        (map τ i).app X := sorry

end iso

end CategoryTheory.Functor.LeftDerived.degree.fromHomotopy
