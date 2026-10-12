/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Setoids.Bicategory

/-!
# `1`-cells of setoid-fibred categories

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

namespace FiberedCategoryOver.Setoids

variable {X Y : FiberedCategoryOver.Setoids C}

/-- The underlying based functor of a morphism of categories fibred in setoids. -/
abbrev toBasedFunctor
    (F : X ⟶ Y) : X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  F.hom

/-- Build a morphism of categories fibred in setoids from a based functor over `C`. This is the
thin bridge to the ambient `BasedFunctor` API. -/
def ofBasedFunctor
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    X ⟶ Y :=
  Bicategory.InducedBicategory.mkHom F

/-- The underlying functor between the total categories. -/
abbrev toFunctor (F : X ⟶ Y) : X.total ⥤ Y.total :=
  (toBasedFunctor F).toFunctor

/-- The strict compatibility of the underlying functor with the two projections to `C`. -/
abbrev comm (F : X ⟶ Y) : toFunctor F ⋙ Y.p = X.p :=
  (toBasedFunctor F).w

/-- The based-functor view of the identity setoid-fibred morphism is the identity based
functor. -/
@[simp]
theorem toBasedFunctor.id (X : FiberedCategoryOver.Setoids C) :
    toBasedFunctor (𝟙 X) = 𝟙 X.toBasedCategory := sorry

/-- The based-functor view preserves composition of setoid-fibred morphisms. -/
@[simp]
theorem toBasedFunctor.comp
    {Z : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    toBasedFunctor (F ≫ G) =
      BasedFunctor.comp (toBasedFunctor F) (toBasedFunctor G) := sorry

/-- The total-category functor underlying the identity morphism of a category fibred in
setoids is the identity functor. -/
@[simp]
theorem toFunctor.id (X : FiberedCategoryOver.Setoids C) :
    toFunctor (𝟙 X) = 𝟭 X.total := sorry

/-- Passing to total-category functors preserves composition of morphisms of categories fibred
in setoids. -/
@[simp]
theorem toFunctor.comp
    {Z : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    toFunctor (F ≫ G) = toFunctor F ⋙ toFunctor G := sorry

/-- The canonical natural isomorphism associated to the strict base-commutativity equation of
a morphism of categories fibred in setoids. -/
def commIso (F : X ⟶ Y) : toFunctor F ⋙ Y.p ≅ X.p :=
  (toBasedFunctor F).projectionIso

/-- Projecting a morphism built by `ofBasedFunctor` recovers the supplied based functor. -/
@[simp]
theorem ofBasedFunctor.toBasedFunctor
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    FiberedCategoryOver.Setoids.toBasedFunctor
      (FiberedCategoryOver.Setoids.ofBasedFunctor F) = F := sorry
/- Proof strategy: unfold `toBasedFunctor` and `ofBasedFunctor`; the induced hom constructor
stores `F` as its ambient object field. -/

/-- The total-category functor of a setoid-fibred morphism built from a based functor is the
supplied functor. -/
@[simp]
theorem ofBasedFunctor.toFunctor
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    FiberedCategoryOver.Setoids.toFunctor
      (FiberedCategoryOver.Setoids.ofBasedFunctor F) = F.toFunctor := sorry

/-- Reconstructing a setoid-fibred morphism from its underlying based functor recovers the
original morphism. -/
@[simp]
theorem toBasedFunctor.ofBasedFunctor (F : X ⟶ Y) :
    ofBasedFunctor (toBasedFunctor F) = F := sorry

/-- Building from the identity based functor gives the identity setoid-fibred morphism. -/
@[simp]
theorem ofBasedFunctor.id (X : FiberedCategoryOver.Setoids C) :
    ofBasedFunctor (𝟙 X.toBasedCategory) = 𝟙 X := sorry

/-- Building from a composite based functor agrees with composition of the corresponding
setoid-fibred morphisms. -/
@[simp]
theorem ofBasedFunctor.comp
    {Z : FiberedCategoryOver.Setoids C}
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (G : Y.toBasedCategory ⥤ᵇ Z.toBasedCategory) :
    ofBasedFunctor (BasedFunctor.comp F G) =
      ofBasedFunctor F ≫ ofBasedFunctor G := sorry

/-- Coerce an owner morphism to its underlying based functor over `C`. -/
instance coeBasedFunctor : CoeOut (X ⟶ Y)
    (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := toBasedFunctor F

end FiberedCategoryOver.Setoids

end CategoryTheory
