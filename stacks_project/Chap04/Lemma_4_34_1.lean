/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fixed.Equivalence

@[expose] public section

universe u v w

namespace CategoryTheory
namespace FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, max w (max u v), v} C}
variable (F : X ⟶ Y)

/- Lemma 4.34.1 (1): in the fixed `2`-category of categories fibred over `C`,
relative inertia is bicategorically equivalent to the self-two-fibre-product of the relative
diagonal, via the canonical comparison. -/
@[stacks 034H "(1)"]
#check (FiberedCategoryOver.RelativeInertia.exists_diagonalComparisonEquivalence F :
  ∃ e : Bicategory.Equivalence (FiberedCategoryOver.relativeInertia F)
      (LocallyInduced.TwoFibreProduct.apex
        (FiberedCategoryOver.RelativeInertia.relativeDiagonal F)
        (FiberedCategoryOver.RelativeInertia.relativeDiagonal F)),
    e.hom = FiberedCategoryOver.RelativeInertia.diagonalComparison F)

/- Lemma 4.34.1 (2): the projection from relative inertia to `C` is fibred. -/
@[stacks 034H "(2)"]
#check (FiberedCategoryOver.RelativeInertia.Projection.Fibered.ofHom F :
  (CategoryTheory.RelativeInertia.projection
    (FiberedCategoryOver.toFunctor F) X.p).IsFibered)

end FiberedCategoryOver
end CategoryTheory
