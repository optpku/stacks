/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_11_3_UniversallyOpen

/-!
# Composition of open morphisms of algebraic stacks

The composition of a pair of open morphisms of algebraic stacks is open,
and the composition of a pair of universally open morphisms of algebraic
stacks is universally open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Open

/-- Lemma 101.11.4 (1): The composition of a pair of open morphisms of
algebraic stacks is open. -/
@[stacks 06U4]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Open f] [Open g] :
    Open (f ≫ g) :=
  sorry

end Open

namespace UniversallyOpen

/-- Lemma 101.11.4 (2): The composition of a pair of universally open
morphisms of algebraic stacks is universally open. -/
@[stacks 06U4]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyOpen f] [UniversallyOpen g] :
    UniversallyOpen (f ≫ g) :=
  sorry

end UniversallyOpen

end AlgebraicGeometry.AlgebraicStack
