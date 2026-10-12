/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_12_2_Submersive

/-!
# Composition of submersive morphisms of algebraic stacks

The composition of a pair of submersive morphisms of algebraic stacks is
submersive, and the composition of a pair of universally submersive morphisms
of algebraic stacks is universally submersive.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Submersive

/-- Lemma 101.12.4 (1): The composition of a pair of submersive morphisms of
algebraic stacks is submersive. -/
@[stacks 0CHZ]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Submersive f] [Submersive g] :
    Submersive (f ≫ g) :=
  sorry

end Submersive

namespace UniversallySubmersive

/-- Lemma 101.12.4 (2): The composition of a pair of universally submersive
morphisms of algebraic stacks is universally submersive. -/
@[stacks 0CHZ]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallySubmersive f] [UniversallySubmersive g] :
    UniversallySubmersive (f ≫ g) :=
  sorry

end UniversallySubmersive

end AlgebraicGeometry.AlgebraicStack
