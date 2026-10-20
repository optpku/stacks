/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Representable
import StacksCheckRecall

/-!
# Existence for representable morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces satisfies the
existence part of the valuative criterion if and only if every scheme-slice
representing morphism of algebraic spaces does.
-/

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.39.13: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `f` satisfies the existence part of
the valuative criterion if and only if for every scheme `T` and morphism
`T ⟶ Y` the morphism `X ×_Y T ⟶ T` satisfies the existence part of the
valuative criterion as a morphism of algebraic spaces. -/
@[stacks 0CLN] #check
  (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence.iff_has :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f →
        (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence f ↔
          Groupoids.Hom.has (@AlgebraicSpace.ValuativeCriterion.Existence S) f))
