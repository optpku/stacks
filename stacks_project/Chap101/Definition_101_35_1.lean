/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Definition 101.35.1: a morphism `f : X ⟶ Y` of algebraic stacks is
étale if it is DM and the equivalent conditions of Lemma 101.34.1 hold with
`P` = étale. -/
@[stacks 0CIL] #check (AlgebraicGeometry.AlgebraicStack.Etale :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)
