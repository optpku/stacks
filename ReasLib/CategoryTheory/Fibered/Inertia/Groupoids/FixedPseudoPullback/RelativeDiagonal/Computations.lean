/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.FixedPseudoPullback.RelativeDiagonal.Construction

/-!
# Fixed groupoid-fibred relative diagonal computations

Componentwise computations for the fixed relative diagonal on objects and
morphisms.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Groupoids.RelativeInertia

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

section FixedPseudoPullbackOwner

variable {X Y :
  FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}

/-- The base component of a groupoid-fibred relative-diagonal object is the image of the
original object under the projection to `C`. -/
@[simp]
theorem relativeDiagonal.obj.base (F : X ⟶ Y) (x : X.total) :
    BasedCategory.PseudoPullback.baseObj
        ((FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F)).obj x) =
      X.p.obj x := sorry

/-- The first component of a groupoid-fibred relative-diagonal object is the original object. -/
@[simp]
theorem relativeDiagonal.obj.fst (F : X ⟶ Y) (x : X.total) :
    BasedCategory.PseudoPullback.fstObj
        ((FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F)).obj x) =
      x := sorry

/-- The second component of a groupoid-fibred relative-diagonal object is the original object. -/
@[simp]
theorem relativeDiagonal.obj.snd (F : X ⟶ Y) (x : X.total) :
    BasedCategory.PseudoPullback.sndObj
        ((FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F)).obj x) =
      x := sorry

/-- The comparison carried by a groupoid-fibred relative-diagonal object is the identity. -/
@[simp]
theorem relativeDiagonal.obj.comparison (F : X ⟶ Y) (x : X.total) :
    BasedCategory.PseudoPullback.comparison
        ((FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F)).obj x) =
      𝟙 ((FiberedCategoryOver.Groupoids.toFunctor F).obj x) := sorry

/-- The complete comparison isomorphism carried by a groupoid-fibred relative-diagonal object
is the identity isomorphism. -/
@[simp]
theorem relativeDiagonal.obj.comparisonIso (F : X ⟶ Y) (x : X.total) :
    BasedCategory.PseudoPullback.comparisonIsoApp
        ((FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F)).obj x) =
      Iso.refl ((FiberedCategoryOver.Groupoids.toFunctor F).obj x) := sorry

/-- The forward component of a fixed groupoid-fibred relative-diagonal comparison is the
identity. -/
@[simp, stacks 034H "groupoid relative diagonal comparison isomorphism hom"]
theorem relativeDiagonal.obj.comparisonIso.hom (F : X ⟶ Y) (x : X.total) :
    (BasedCategory.PseudoPullback.comparisonIsoApp
      ((FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F)).obj x)).hom =
      𝟙 ((FiberedCategoryOver.Groupoids.toFunctor F).obj x) := sorry

/-- The inverse component of a fixed groupoid-fibred relative-diagonal comparison is the
identity. -/
@[simp, stacks 034H "groupoid relative diagonal comparison isomorphism inverse"]
theorem relativeDiagonal.obj.comparisonIso.inv (F : X ⟶ Y) (x : X.total) :
    (BasedCategory.PseudoPullback.comparisonIsoApp
      ((FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F)).obj x)).inv =
      𝟙 ((FiberedCategoryOver.Groupoids.toFunctor F).obj x) := sorry

/-- The base component of a groupoid-fibred relative-diagonal morphism is its image under the
original projection. -/
@[simp]
theorem relativeDiagonal.map.base
    (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    BasedCategory.PseudoPullback.baseMap
        ((FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F)).map f) =
      X.p.map f := sorry

/-- The first component of a groupoid-fibred relative-diagonal morphism is the original
morphism. -/
@[simp]
theorem relativeDiagonal.map.fst
    (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    BasedCategory.PseudoPullback.fstMap
        ((FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F)).map f) =
      f := sorry

/-- The second component of a groupoid-fibred relative-diagonal morphism is the original
morphism. -/
@[simp]
theorem relativeDiagonal.map.snd
    (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    BasedCategory.PseudoPullback.sndMap
        ((FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F)).map f) =
      f := sorry

/-- A fixed groupoid-fibred relative-diagonal morphism satisfies the comparison square of its two
identical legs. -/
@[stacks 034H "groupoid relative diagonal map square"]
theorem relativeDiagonal.map.comm
    (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    CommSq
      ((FiberedCategoryOver.Groupoids.toFunctor F).map f)
      (BasedCategory.PseudoPullback.comparison
        ((FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F)).obj x))
      (BasedCategory.PseudoPullback.comparison
        ((FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F)).obj y))
      ((FiberedCategoryOver.Groupoids.toFunctor F).map f) := sorry

/-- The comparison arrows of fixed groupoid-fibred relative-diagonal objects are natural in source
morphisms. -/
@[reassoc, stacks 034H "groupoid relative diagonal map naturality"]
theorem relativeDiagonal.map.naturality
    (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    (FiberedCategoryOver.Groupoids.toFunctor F).map f ≫
        BasedCategory.PseudoPullback.comparison
          ((FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F)).obj y) =
      BasedCategory.PseudoPullback.comparison
          ((FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F)).obj x) ≫
        (FiberedCategoryOver.Groupoids.toFunctor F).map f := sorry

/-- The first fixed two-fibre-product projection of the groupoid-fibred relative diagonal is
the identity morphism. -/
@[simp, stacks 034H "groupoid relative diagonal first projection"]
theorem relativeDiagonal.fst (F : X ⟶ Y) :
    relativeDiagonal F ≫ CategoryTheory.TwoFibreProduct.fst F F = 𝟙 X := sorry

/-- The second fixed two-fibre-product projection of the groupoid-fibred relative diagonal is
the identity morphism. -/
@[simp, stacks 034H "groupoid relative diagonal second projection"]
theorem relativeDiagonal.snd (F : X ⟶ Y) :
    relativeDiagonal F ≫ CategoryTheory.TwoFibreProduct.snd F F = 𝟙 X := sorry

end FixedPseudoPullbackOwner

end FiberedCategoryOver.Groupoids.RelativeInertia

end CategoryTheory
