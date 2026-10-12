/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_25_5_Flat

/-!
# Composition of flat morphisms of algebraic stacks

The composition of a pair of flat morphisms of algebraic stacks is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Flat

/-- Lemma 101.25.2: The composition of flat morphisms of algebraic stacks is
flat. -/
@[stacks 06PX]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    Flat (f ≫ g) :=
  sorry

end Flat

end AlgebraicGeometry.AlgebraicStack
