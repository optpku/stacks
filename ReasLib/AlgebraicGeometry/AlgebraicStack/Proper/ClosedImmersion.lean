/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed immersions of algebraic stacks are proper

A closed immersion of algebraic stacks is a proper morphism of algebraic
stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Proper

/-- A closed immersion of algebraic stacks is a proper morphism of algebraic
stacks. -/
@[stacks 0CL8]
instance of_closedImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f] :
    Proper f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Proper
