/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack
import StacksCheckRecall

/-!
# Image of an immersion of algebraic stacks

An immersion of algebraic stacks factors uniquely through a locally closed
substack of the target, namely the essential image of the underlying total
functor. Closed and open immersions yield closed and open substacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 100.9.10 (1): For any immersion `i : Z ⟶ X` there exists a unique
locally closed substack `X' ⊂ X` such that `i` factors as the composition of
an equivalence `i' : Z ⟶ X'` followed by the inclusion `X' ⟶ X`. The
canonical such substack is the essential-image full subcategory.
Uniqueness is equality of object properties. -/
@[stacks 0506]
#check (AlgebraicGeometry.AlgebraicStack.existsUnique_image :
  ∀ {S : Scheme.{u}} {Z X : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack X]
    (i : Z ⟶ X) [Immersion i],
    AlgebraicStack.Substack.IsLocallyClosed X (toFunctor i).essImage ∧
      AlgebraicStack.Substack.IsImage i (toFunctor i).essImage ∧
        ∀ P : ObjectProperty X.total,
          AlgebraicStack.Substack.IsLocallyClosed X P →
            AlgebraicStack.Substack.IsImage i P → P = (toFunctor i).essImage)

/- Lemma 100.9.10 (2): If `i` is a closed immersion, then the unique locally
closed image of `i` is a closed substack of `X`. -/
@[stacks 0506]
#check (AlgebraicGeometry.AlgebraicStack.image_isClosed :
  ∀ {S : Scheme.{u}} {Z X : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack X]
    (i : Z ⟶ X) [ClosedImmersion i],
    AlgebraicStack.Substack.IsClosed X (toFunctor i).essImage)

/- Lemma 100.9.10 (3): If `i` is an open immersion, then the unique locally
closed image of `i` is an open substack of `X`. -/
@[stacks 0506]
#check (AlgebraicGeometry.AlgebraicStack.image_isOpen :
  ∀ {S : Scheme.{u}} {Z X : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack X]
    (i : Z ⟶ X) [OpenImmersion i],
    AlgebraicStack.Substack.IsOpen X (toFunctor i).essImage)

