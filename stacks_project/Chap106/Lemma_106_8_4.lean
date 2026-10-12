/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Definition_106_8_1_FormallySmooth

/-!
# Composition of formally smooth morphisms of algebraic stacks

The composition of formally smooth morphisms of algebraic stacks is formally
smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 106.8.4. The composition of formally smooth morphisms of algebraic
stacks is formally smooth. -/
@[stacks 0H1J]
instance FormallySmooth.comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [FormallySmooth f] [FormallySmooth g] :
    FormallySmooth (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
