/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed.Composition
import StacksCheckRecall

/-!
# Composition of closed morphisms of algebraic stacks

The composition of a pair of closed morphisms of algebraic stacks is closed,
and the composition of a pair of universally closed morphisms of algebraic
stacks is universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.13.4 (1): The composition of a pair of closed morphisms of
algebraic stacks is closed. -/
@[stacks 0515] #check (AlgebraicGeometry.AlgebraicStack.Closed.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Closed f] [Closed g],
    Closed (f ≫ g))

/- Lemma 101.13.4 (2): The composition of a pair of universally closed
morphisms of algebraic stacks is universally closed. -/
@[stacks 0515] #check (AlgebraicGeometry.AlgebraicStack.UniversallyClosed.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyClosed f] [UniversallyClosed g],
    UniversallyClosed (f ≫ g))

end AlgebraicGeometry.AlgebraicStack
