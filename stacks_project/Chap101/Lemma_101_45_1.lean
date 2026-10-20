/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.StabilizerPreserving

/-!
# Stabilizer-preserving morphisms of algebraic stacks

If the canonical inertia comparison `I_X ⟶ X ×_Y I_Y` of a morphism of
algebraic stacks is an isomorphism, then the morphism is representable by
algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.45.1: let `f : X ⟶ Y` be a morphism of algebraic stacks. If the
canonical 1-morphism `Inertia.comparison f : I_X ⟶ X ×_Y I_Y` is an
isomorphism of stacks, then `f` is representable by algebraic spaces. In the
literature this comparison being an isomorphism is the condition that `f` is
stabilizer preserving or fixed-point reflecting. -/
@[stacks 0DU7] #check
  (AlgebraicGeometry.AlgebraicStack.relativelyRepresentableByAlgebraicSpaces_of_isEquivalence_comparison :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
      [AlgebraicStack Y] (f : X ⟶ Y),
      (toBasedFunctor (Inertia.comparison f)).IsEquivalence →
        relativelyRepresentableByAlgebraicSpaces f)

end AlgebraicGeometry.AlgebraicStack
