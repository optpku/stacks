/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_36_4_Unramified
public import stacks_project.Chap101.Definition_101_23_2_LocallyQuasiFinite

/-!
# Unramified morphisms of algebraic stacks are locally quasi-finite
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.36.7: An unramified morphism of algebraic stacks is locally
quasi-finite. -/
@[stacks 0H2Z]
instance locallyQuasiFinite_of_unramified {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Unramified f] :
    LocallyQuasiFinite f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
