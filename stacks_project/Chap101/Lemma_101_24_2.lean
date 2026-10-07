module

public import stacks_project.Chap101.Definition_101_24_1_QuasiFinite

/-!
# Composition of quasi-finite morphisms of algebraic stacks

A composition of quasi-finite morphisms of algebraic stacks is quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiFinite

/-- Lemma 101.24.2: A composition of quasi-finite morphisms is quasi-finite.

Stacks writes the composition as `g ∘ f`; the Lean composite is `f ≫ g`. -/
@[stacks 0G2N]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiFinite f] [QuasiFinite g] :
    QuasiFinite (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiFinite
