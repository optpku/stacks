/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InSets.Bicategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# `1`-cells of set-fibred categories

Underlying based and total functors, their constructors, and identity/composition computations.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open ObjectProperty
open BasedFunctor
open BasedCategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets

variable {X Y : FiberedCategoryOver.Sets C}

/-- Build a morphism of categories fibred in sets directly from a based functor over `C`. -/
@[stacks 04S8 "morphism constructor for categories fibred in sets"]
def ofBasedFunctor
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    X ⟶ Y :=
  Bicategory.InducedBicategory.mkHom F

/-- The underlying based functor of a morphism of categories fibred in sets. -/
abbrev toBasedFunctor
    (F : X ⟶ Y) :
    X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  F.hom

/-- The underlying functor between the total categories. -/
abbrev toFunctor (F : X ⟶ Y) : X.total ⥤ Y.total :=
  (toBasedFunctor F).toFunctor

/-- The strict compatibility of the underlying functor with the two projections to `C`. -/
abbrev comm (F : X ⟶ Y) : toFunctor F ⋙ Y.p = X.p :=
  (toBasedFunctor F).w

/-- The based-functor view of the identity set-fibred morphism is the identity based functor. -/
@[simp]
theorem toBasedFunctor.id (X : FiberedCategoryOver.Sets C) :
    toBasedFunctor (𝟙 X) = 𝟙 X.toBasedCategory := rfl

/-- The based-functor view preserves composition of set-fibred morphisms. -/
@[simp]
theorem toBasedFunctor.comp
    {Z : FiberedCategoryOver.Sets C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    toBasedFunctor (F ≫ G) =
      BasedFunctor.comp (toBasedFunctor F) (toBasedFunctor G) := rfl

/-- The total-category functor underlying the identity morphism of a category fibred in sets is
the identity functor. -/
@[simp]
theorem toFunctor.id (X : FiberedCategoryOver.Sets C) :
    toFunctor (𝟙 X) = 𝟭 X.total := rfl

/-- Passing to total-category functors preserves composition of morphisms of categories fibred
in sets. -/
@[simp]
theorem toFunctor.comp
    {Z : FiberedCategoryOver.Sets C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    toFunctor (F ≫ G) = toFunctor F ⋙ toFunctor G := rfl

/-- The canonical natural isomorphism associated to the strict base-commutativity equation of
a morphism of categories fibred in sets. -/
@[stacks 04S8 "projection compatibility for a morphism fibred in sets"]
def commIso (F : X ⟶ Y) : toFunctor F ⋙ Y.p ≅ X.p :=
  (toBasedFunctor F).projectionIso

/-- Projecting a morphism built by `ofBasedFunctor` recovers the supplied based functor. -/
@[simp]
theorem ofBasedFunctor.toBasedFunctor
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    FiberedCategoryOver.Sets.toBasedFunctor
      (FiberedCategoryOver.Sets.ofBasedFunctor F) = F := rfl
/- Proof strategy: unfold `toBasedFunctor` and `ofBasedFunctor`; the induced hom constructor
stores `F` as its ambient object field. -/

/-- The total-category functor of a morphism built from a based functor is the supplied functor. -/
@[simp]
theorem ofBasedFunctor.toFunctor
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    FiberedCategoryOver.Sets.toFunctor
      (FiberedCategoryOver.Sets.ofBasedFunctor F) = F.toFunctor := rfl

/-- Reconstructing a set-fibred morphism from its underlying based functor recovers the original
morphism. -/
@[simp]
theorem toBasedFunctor.ofBasedFunctor (F : X ⟶ Y) :
    ofBasedFunctor (toBasedFunctor F) = F := rfl

/-- Building from the identity based functor gives the identity set-fibred morphism. -/
@[simp]
theorem ofBasedFunctor.id (X : FiberedCategoryOver.Sets C) :
    ofBasedFunctor (𝟙 X.toBasedCategory) = 𝟙 X := rfl

/-- Building from a composite based functor agrees with composition of the corresponding
set-fibred morphisms. -/
@[simp]
theorem ofBasedFunctor.comp
    {Z : FiberedCategoryOver.Sets C}
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (G : Y.toBasedCategory ⥤ᵇ Z.toBasedCategory) :
    ofBasedFunctor (BasedFunctor.comp F G) =
      ofBasedFunctor F ≫ ofBasedFunctor G := rfl

/-- Coerce an owner morphism to its underlying based functor over `C`. -/
instance coeBasedFunctor : CoeOut (X ⟶ Y)
    (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := toBasedFunctor F

end FiberedCategoryOver.Sets

end CategoryTheory
