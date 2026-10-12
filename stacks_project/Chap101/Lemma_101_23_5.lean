/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_23_2_LocallyQuasiFinite

/-!
# Composition of locally quasi-finite morphisms of algebraic stacks

A composition of locally quasi-finite morphisms of algebraic stacks is
locally quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite

/-- Lemma 101.23.5: A composition of locally quasi-finite morphisms is
locally quasi-finite.

Stacks writes the composition as `g ∘ f`; the Lean composite is `f ≫ g`. -/
@[stacks 06UD]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyQuasiFinite f] [LocallyQuasiFinite g] :
    LocallyQuasiFinite (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
