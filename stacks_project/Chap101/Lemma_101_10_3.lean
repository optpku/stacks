/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_10_1_Integral

/-!
# Composition of integral and finite morphisms of algebraic stacks

The composition of a pair of integral morphisms of algebraic stacks is
integral, and the composition of a pair of finite morphisms of algebraic
stacks is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace IsIntegralHom

/-- Lemma 101.10.3 (1): compositions of integral morphisms of algebraic stacks
are integral. -/
@[stacks 0CHW]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegralHom f] [IsIntegralHom g] :
    IsIntegralHom (f ≫ g) :=
  sorry

end IsIntegralHom

namespace IsFinite

/-- Lemma 101.10.3 (2): compositions of finite morphisms of algebraic stacks
are finite. -/
@[stacks 0CHW]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [IsFinite g] :
    IsFinite (f ≫ g) :=
  sorry

end IsFinite

end AlgebraicGeometry.AlgebraicStack
