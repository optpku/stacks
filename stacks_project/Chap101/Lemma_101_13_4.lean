/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_13_2_Closed

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

namespace Closed

/-- Lemma 101.13.4 (1): The composition of a pair of closed morphisms of
algebraic stacks is closed. -/
@[stacks 0515]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Closed f] [Closed g] :
    Closed (f ≫ g) :=
  sorry

end Closed

namespace UniversallyClosed

/-- Lemma 101.13.4 (2): The composition of a pair of universally closed
morphisms of algebraic stacks is universally closed. -/
@[stacks 0515]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyClosed f] [UniversallyClosed g] :
    UniversallyClosed (f ≫ g) :=
  sorry

end UniversallyClosed

end AlgebraicGeometry.AlgebraicStack
