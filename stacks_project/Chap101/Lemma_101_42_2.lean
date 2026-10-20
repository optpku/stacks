/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.UniversallyClosed
import StacksCheckRecall

/-!
# Valuative criterion for universal closedness

A quasi-separated universally closed morphism of algebraic stacks satisfies the
existence part of the valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.42.2: A quasi-separated universally closed morphism of algebraic
stacks satisfies the existence part of the valuative criterion. -/
@[stacks 0CLX] #check
  (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence.of_universallyClosed :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y), [AlgebraicGeometry.AlgebraicStack.QuasiSeparated f] →
      [AlgebraicGeometry.AlgebraicStack.UniversallyClosed f] →
      AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Existence f)
