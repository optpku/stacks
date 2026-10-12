/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_14_2_UniversallyInjective

/-!
# Composition of universally injective morphisms of algebraic stacks

The composition of a pair of universally injective morphisms of algebraic
stacks is universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversallyInjective

/-- Lemma 101.14.4: The composition of a pair of universally injective
morphisms of algebraic stacks is universally injective. -/
@[stacks 0CI4]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyInjective f] [UniversallyInjective g] :
    UniversallyInjective (f ≫ g) :=
  sorry

end UniversallyInjective

end AlgebraicGeometry.AlgebraicStack
