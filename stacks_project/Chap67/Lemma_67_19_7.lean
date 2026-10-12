/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of universally injective morphisms of algebraic spaces

The composition of a pair of universally injective morphisms of algebraic spaces
is universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.19.7: The composition of universally injective morphisms of algebraic
spaces is universally injective. -/
@[stacks 03MY]
instance universallyInjective_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@UniversallyInjective S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of universally injective morphisms of algebraic spaces is
universally injective. -/
instance universallyInjective_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyInjective f] [UniversallyInjective g] :
    UniversallyInjective (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
