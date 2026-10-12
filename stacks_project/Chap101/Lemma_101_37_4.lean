/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap101.Definition_101_37_1_Proper

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

/-- Lemma 101.37.4: A closed immersion of algebraic stacks is a proper morphism
of algebraic stacks. -/
@[stacks 0CL8]
instance of_closedImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f] :
    Proper f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Proper
