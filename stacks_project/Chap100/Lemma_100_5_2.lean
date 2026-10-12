/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_5_1_Surjective

/-!
# Composition of surjective morphisms of algebraic stacks

The composition of a pair of surjective morphisms of algebraic stacks is
surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Surjective

/-- Lemma 100.5.2: The composition of surjective morphisms is surjective. -/
@[stacks 04ZT]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [Surjective g] :
    Surjective (f ≫ g) :=
  sorry

end Surjective

end AlgebraicGeometry.AlgebraicStack
