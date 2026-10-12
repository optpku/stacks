/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fixed.Comparison.Construction

/-!
# Fibred relative-inertia comparison computations

Projection and automorphism readouts for the fixed fibred-category comparison.
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

/-- The base projection of a fibred relative-inertia comparison object is the base of its
underlying inertia object. -/
@[simp]
theorem diagonalComparison.obj.base
    (F : X ⟶ Y) (A : (relativeInertia F).total) :
    BasedCategory.PseudoPullback.baseObj
        ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison F)).obj A) =
      X.p.obj A.obj := sorry

/-- The first projection of a fibred relative-inertia comparison object is its underlying
total-category object. -/
@[simp]
theorem diagonalComparison.obj.fst
    (F : X ⟶ Y) (A : (relativeInertia F).total) :
    BasedCategory.PseudoPullback.fstObj
        ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison F)).obj A) =
      A.obj := sorry

/-- The second projection of a fibred relative-inertia comparison object is its underlying
total-category object. -/
@[simp]
theorem diagonalComparison.obj.snd
    (F : X ⟶ Y) (A : (relativeInertia F).total) :
    BasedCategory.PseudoPullback.sndObj
        ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison F)).obj A) =
      A.obj := sorry

/-- The base projection of a fibred relative-inertia comparison morphism is the projection of
its underlying inertia arrow. -/
@[simp]
theorem diagonalComparison.map.base
    (F : X ⟶ Y) {A B : (relativeInertia F).total} (φ : A ⟶ B) :
    BasedCategory.PseudoPullback.baseMap
        ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison F)).map φ) =
      X.p.map (CategoryTheory.RelativeInertia.hom φ) := sorry

/-- The first projection of a fibred relative-inertia comparison morphism is its underlying
inertia arrow. -/
@[simp]
theorem diagonalComparison.map.fst
    (F : X ⟶ Y) {A B : (relativeInertia F).total} (φ : A ⟶ B) :
    BasedCategory.PseudoPullback.fstMap
        ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison F)).map φ) =
      CategoryTheory.RelativeInertia.hom φ := sorry

/-- The second projection of a fibred relative-inertia comparison morphism is its underlying
inertia arrow. -/
@[simp]
theorem diagonalComparison.map.snd
    (F : X ⟶ Y) {A B : (relativeInertia F).total} (φ : A ⟶ B) :
    BasedCategory.PseudoPullback.sndMap
        ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison F)).map φ) =
      CategoryTheory.RelativeInertia.hom φ := sorry

/-- A fibred relative-inertia comparison morphism forms the expected square between the
comparison automorphisms of its endpoints. -/
theorem diagonalComparison.map.comm
    (F : X ⟶ Y) {A B : (relativeInertia F).total} (φ : A ⟶ B) :
    CommSq
      ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).map
        (CategoryTheory.RelativeInertia.hom φ))
      (BasedCategory.PseudoPullback.comparison
        ((FiberedCategoryOver.toFunctor
          (RelativeInertia.diagonalComparison F)).obj A))
      (BasedCategory.PseudoPullback.comparison
        ((FiberedCategoryOver.toFunctor
          (RelativeInertia.diagonalComparison F)).obj B))
      ((FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).map
        (CategoryTheory.RelativeInertia.hom φ)) := sorry

/-- The comparison automorphisms commute with the typed relative-diagonal image of every
relative-inertia morphism. -/
@[reassoc]
theorem diagonalComparison.map.naturality
    (F : X ⟶ Y) {A B : (relativeInertia F).total} (φ : A ⟶ B) :
    (FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).map
        (CategoryTheory.RelativeInertia.hom φ) ≫
      BasedCategory.PseudoPullback.comparison
        ((FiberedCategoryOver.toFunctor
          (RelativeInertia.diagonalComparison F)).obj B) =
    BasedCategory.PseudoPullback.comparison
        ((FiberedCategoryOver.toFunctor
          (RelativeInertia.diagonalComparison F)).obj A) ≫
      (FiberedCategoryOver.toFunctor (RelativeInertia.relativeDiagonal F)).map
        (CategoryTheory.RelativeInertia.hom φ) := sorry

/-- The base component of the comparison stored by a fibred relative-inertia comparison object
is an identity. -/
@[simp]
theorem diagonalComparison.obj.aut.base
    (F : X ⟶ Y) (A : (relativeInertia F).total) :
    BasedCategory.PseudoPullback.baseMap
        (BasedCategory.PseudoPullback.comparison
          ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison F)).obj A)) =
      𝟙 (X.p.obj A.obj) := sorry

/-- The first component of the comparison stored by a fibred relative-inertia comparison object
is its selected automorphism. -/
@[simp]
theorem diagonalComparison.obj.aut.fst
    (F : X ⟶ Y) (A : (relativeInertia F).total) :
    BasedCategory.PseudoPullback.fstMap
        (BasedCategory.PseudoPullback.comparison
          ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison F)).obj A)) =
      A.aut.hom := sorry

/-- The second component of the comparison stored by a fibred relative-inertia comparison
object is an identity. -/
@[simp]
theorem diagonalComparison.obj.aut.snd
    (F : X ⟶ Y) (A : (relativeInertia F).total) :
    BasedCategory.PseudoPullback.sndMap
        (BasedCategory.PseudoPullback.comparison
          ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison F)).obj A)) =
      𝟙 A.obj := sorry

/-- The inverse comparison stored by a fibred relative-inertia object has identity base
component. -/
@[simp]
theorem diagonalComparison.obj.aut.inv.base
    (F : X ⟶ Y) (A : (relativeInertia F).total) :
    BasedCategory.PseudoPullback.baseMap
        (BasedCategory.PseudoPullback.comparisonIsoApp
          ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison F)).obj A)).inv =
      𝟙 (X.p.obj A.obj) := sorry

/-- The first inverse comparison component of a fibred relative-inertia object is its inverse
selected automorphism. -/
@[simp]
theorem diagonalComparison.obj.aut.inv.fst
    (F : X ⟶ Y) (A : (relativeInertia F).total) :
    BasedCategory.PseudoPullback.fstMap
        (BasedCategory.PseudoPullback.comparisonIsoApp
          ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison F)).obj A)).inv =
      A.aut.inv := sorry

/-- The second inverse comparison component of a fibred relative-inertia object is an identity. -/
@[simp]
theorem diagonalComparison.obj.aut.inv.snd
    (F : X ⟶ Y) (A : (relativeInertia F).total) :
    BasedCategory.PseudoPullback.sndMap
        (BasedCategory.PseudoPullback.comparisonIsoApp
          ((FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison F)).obj A)).inv =
      𝟙 A.obj := sorry

end FixedOwner

end FiberedCategoryOver.RelativeInertia
end CategoryTheory
