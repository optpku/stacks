/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact

/-!
# Composition of quasi-compact morphisms of algebraic stacks

The composition of a pair of quasi-compact morphisms of algebraic stacks is
quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.7.4: The composition of a pair of quasi-compact morphisms of
algebraic stacks is quasi-compact. -/
@[stacks 050W]
instance quasiCompact_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g] :
    QuasiCompact (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
