/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair.Presentation
import StacksCheckRecall

/-!
# Lemma 94.16.2

A surjective smooth 1-morphism from an algebraic space into an algebraic stack
yields a smooth kernel-pair groupoid and an equivalence from the quotient stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 94.16.2 (1): the morphisms s, t of the kernel-pair groupoid (U, R, s, t, c)
are smooth. -/
@[stacks 04T5]
#check (AlgebraicGeometry.AlgebraicStack.groupoid_smooth :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Smooth f] [Groupoids.Hom.Surjective f],
    GroupoidAlgebraicSpace.Smooth (AlgebraicGeometry.AlgebraicStack.groupoid f hU))

/- Lemma 94.16.2 (2): the 1-morphism f_can : [U/R] ⟶ X is an equivalence. -/
@[stacks 04T5]
#check (AlgebraicGeometry.AlgebraicStack.fCan_isEquivalence :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Smooth f] [Groupoids.Hom.Surjective f],
    (toBasedFunctor (AlgebraicGeometry.AlgebraicStack.fCan f hU)).IsEquivalence)

