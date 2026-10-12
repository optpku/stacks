/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fixed.RelativeDiagonal.Construction

/-!
# Fibred relative diagonal computations

Projection readouts for the fixed fibred-category relative diagonal.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.RelativeInertia

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

section FixedOwner

variable {X Y :
  FiberedCategoryOver.{u, v, max w (max u v), v} C}

/-- The base component of a fibred relative-diagonal object is the image of the original
object under the projection to `C`. -/
@[simp]
theorem relativeDiagonal.obj.base (F : X ⟶ Y) (x : X.total) :
    BasedCategory.PseudoPullback.baseObj
        ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).obj x) =
      X.p.obj x := sorry

/-- The first component of a fibred relative-diagonal object is the original object. -/
@[simp]
theorem relativeDiagonal.obj.fst (F : X ⟶ Y) (x : X.total) :
    BasedCategory.PseudoPullback.fstObj
        ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).obj x) =
      x := sorry

/-- The second component of a fibred relative-diagonal object is the original object. -/
@[simp]
theorem relativeDiagonal.obj.snd (F : X ⟶ Y) (x : X.total) :
    BasedCategory.PseudoPullback.sndObj
        ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).obj x) =
      x := sorry

/-- The comparison carried by a fibred relative-diagonal object is the identity. -/
@[simp]
theorem relativeDiagonal.obj.comparison (F : X ⟶ Y) (x : X.total) :
    BasedCategory.PseudoPullback.comparison
        ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).obj x) =
      𝟙 ((FiberedCategoryOver.toFunctor F).obj x) := sorry

/-- The complete comparison isomorphism carried by a fibred relative-diagonal object is the
identity isomorphism. -/
@[simp]
theorem relativeDiagonal.obj.comparisonIso (F : X ⟶ Y) (x : X.total) :
    BasedCategory.PseudoPullback.comparisonIsoApp
        ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).obj x) =
      Iso.refl ((FiberedCategoryOver.toFunctor F).obj x) := sorry

/-- The forward component of a fixed fibred relative-diagonal comparison is the identity. -/
@[simp, stacks 034H "fixed relative diagonal comparison isomorphism hom"]
theorem relativeDiagonal.obj.comparisonIso.hom (F : X ⟶ Y) (x : X.total) :
    (BasedCategory.PseudoPullback.comparisonIsoApp
      ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).obj x)).hom =
      𝟙 ((FiberedCategoryOver.toFunctor F).obj x) := sorry

/-- The inverse component of a fixed fibred relative-diagonal comparison is the identity. -/
@[simp, stacks 034H "fixed relative diagonal comparison isomorphism inverse"]
theorem relativeDiagonal.obj.comparisonIso.inv (F : X ⟶ Y) (x : X.total) :
    (BasedCategory.PseudoPullback.comparisonIsoApp
      ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).obj x)).inv =
      𝟙 ((FiberedCategoryOver.toFunctor F).obj x) := sorry

/-- The base component of a fibred relative-diagonal morphism is its image under the original
projection. -/
@[simp]
theorem relativeDiagonal.map.base
    (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    BasedCategory.PseudoPullback.baseMap
        ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).map f) =
      X.p.map f := sorry

/-- The first component of a fibred relative-diagonal morphism is the original morphism. -/
@[simp]
theorem relativeDiagonal.map.fst
    (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    BasedCategory.PseudoPullback.fstMap
        ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).map f) =
      f := sorry

/-- The second component of a fibred relative-diagonal morphism is the original morphism. -/
@[simp]
theorem relativeDiagonal.map.snd
    (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    BasedCategory.PseudoPullback.sndMap
        ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).map f) =
      f := sorry

/-- A fixed fibred relative-diagonal morphism satisfies the comparison square of its two
identical legs. -/
@[stacks 034H "fixed relative diagonal map square"]
theorem relativeDiagonal.map.comm
    (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    CommSq
      ((FiberedCategoryOver.toFunctor F).map f)
      (BasedCategory.PseudoPullback.comparison
        ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).obj x))
      (BasedCategory.PseudoPullback.comparison
        ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).obj y))
      ((FiberedCategoryOver.toFunctor F).map f) := sorry

/-- The comparison arrows of fixed fibred relative-diagonal objects are natural in source
morphisms. -/
@[reassoc, stacks 034H "fixed relative diagonal map naturality"]
theorem relativeDiagonal.map.naturality
    (F : X ⟶ Y) {x y : X.total} (f : x ⟶ y) :
    (FiberedCategoryOver.toFunctor F).map f ≫
        BasedCategory.PseudoPullback.comparison
          ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).obj y) =
      BasedCategory.PseudoPullback.comparison
          ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).obj x) ≫
        (FiberedCategoryOver.toFunctor F).map f := sorry

/-- The first fixed two-fibre-product projection of the fibred relative diagonal is the
identity morphism. -/
@[simp, stacks 034H "fixed relative diagonal first projection"]
theorem relativeDiagonal.fst (F : X ⟶ Y) :
    RelativeInertia.relativeDiagonal F ≫
        LocallyInduced.TwoFibreProduct.fst F F =
      𝟙 X := sorry

/-- The second fixed two-fibre-product projection of the fibred relative diagonal is the
identity morphism. -/
@[simp, stacks 034H "fixed relative diagonal second projection"]
theorem relativeDiagonal.snd (F : X ⟶ Y) :
    RelativeInertia.relativeDiagonal F ≫
        LocallyInduced.TwoFibreProduct.snd F F =
      𝟙 X := sorry

end FixedOwner

end FiberedCategoryOver.RelativeInertia
end CategoryTheory
