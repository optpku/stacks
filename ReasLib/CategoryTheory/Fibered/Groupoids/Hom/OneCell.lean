/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory

/-!
# `1`-cells of groupoid-fibred categories

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

namespace FiberedCategoryOver.Groupoids

variable {X Y : FiberedCategoryOver.Groupoids C}

/-- The underlying based functor of a morphism of categories fibred in groupoids over `C`. -/
abbrev toBasedFunctor (F : X ⟶ Y) : X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  F.hom

/-- The canonical cartesian based functor underlying a morphism of categories fibred in
groupoids. Cartesian preservation is supplied by the groupoid-fibred target. -/
def toCartesianBasedFunctor (F : X ⟶ Y) : CartesianBasedFunctor X.p Y.p :=
  CartesianBasedFunctor.ofTargetInGroupoids (toBasedFunctor F)

/-- Forgetting cartesian preservation recovers the underlying based functor. -/
@[simp]
theorem toCartesianBasedFunctor.toBasedFunctor (F : X ⟶ Y) :
    (toCartesianBasedFunctor F).toBasedFunctor = toBasedFunctor F := sorry

/-- The underlying functor between the total categories. -/
abbrev toFunctor (F : X ⟶ Y) : X.total ⥤ Y.total :=
  toBasedFunctor F |>.toFunctor

/-- The compatibility of the underlying functor with the base projections. -/
abbrev comm (F : X ⟶ Y) : toFunctor F ⋙ Y.p = X.p :=
  toBasedFunctor F |>.w

/-- The based-functor view of the identity groupoid-fibred morphism is the identity based
functor. -/
@[simp]
theorem toBasedFunctor.id (X : FiberedCategoryOver.Groupoids C) :
    toBasedFunctor (𝟙 X) = 𝟙 X.toBasedCategory := sorry

/-- The based-functor view preserves composition of groupoid-fibred morphisms. -/
@[simp]
theorem toBasedFunctor.comp
    {Z : FiberedCategoryOver.Groupoids C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    toBasedFunctor (F ≫ G) =
      BasedFunctor.comp (toBasedFunctor F) (toBasedFunctor G) := sorry

/-- The total-category functor underlying the identity morphism of a category fibred in
groupoids is the identity functor. -/
@[simp]
theorem toFunctor.id (X : FiberedCategoryOver.Groupoids C) :
    toFunctor (𝟙 X) = 𝟭 X.total := sorry

/-- Passing to total-category functors preserves composition of morphisms of categories fibred
in groupoids. -/
@[simp]
theorem toFunctor.comp
    {Z : FiberedCategoryOver.Groupoids C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    toFunctor (F ≫ G) = toFunctor F ⋙ toFunctor G := sorry

/-- The canonical natural isomorphism associated to the strict base-commutativity equation of
a morphism of categories fibred in groupoids. This is the stable bridge for constructions whose
square input is formulated up to isomorphism. -/
def commIso (F : X ⟶ Y) : toFunctor F ⋙ Y.p ≅ X.p :=
  (toBasedFunctor F).projectionIso

/-- Compatibility coercion from owner homs to based functors over `C`. -/
instance coeBasedFunctor : CoeOut (X ⟶ Y) (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := toBasedFunctor F

/-- Build a morphism of categories fibred in groupoids over `C` from a based functor over `C`.
This is the thin bridge from the owner-selected homs to the ambient `BasedFunctor` API. -/
def ofBasedFunctor
    (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    X ⟶ Y :=
  Bicategory.InducedBicategory.mkHom G

/-- Projecting a morphism built by `ofBasedFunctor` recovers the supplied based functor. -/
@[simp]
theorem ofBasedFunctor.toBasedFunctor
    (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    FiberedCategoryOver.Groupoids.toBasedFunctor
      (FiberedCategoryOver.Groupoids.ofBasedFunctor G) = G := sorry
/- Proof strategy: unfold `toBasedFunctor` and `ofBasedFunctor`; the induced hom constructor
stores `G` as its ambient object field. -/

/-- The total-category functor of a groupoid-fibred morphism built from a based functor is the
supplied functor. -/
@[simp]
theorem ofBasedFunctor.toFunctor
    (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    FiberedCategoryOver.Groupoids.toFunctor
      (FiberedCategoryOver.Groupoids.ofBasedFunctor G) = G.toFunctor := sorry

/-- Reconstructing a groupoid-fibred morphism from its underlying based functor recovers the
original morphism. -/
@[simp]
theorem toBasedFunctor.ofBasedFunctor (F : X ⟶ Y) :
    ofBasedFunctor (toBasedFunctor F) = F := sorry

/-- Building from the identity based functor gives the identity groupoid-fibred morphism. -/
@[simp]
theorem ofBasedFunctor.id (X : FiberedCategoryOver.Groupoids C) :
    ofBasedFunctor (𝟙 X.toBasedCategory) = 𝟙 X := sorry

/-- Building from a composite based functor agrees with composition of the corresponding
groupoid-fibred morphisms. -/
@[simp]
theorem ofBasedFunctor.comp
    {Z : FiberedCategoryOver.Groupoids C}
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (G : Y.toBasedCategory ⥤ᵇ Z.toBasedCategory) :
    ofBasedFunctor (BasedFunctor.comp F G) =
      ofBasedFunctor F ≫ ofBasedFunctor G := sorry

end FiberedCategoryOver.Groupoids

end CategoryTheory
