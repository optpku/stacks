/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of universal homeomorphisms of algebraic spaces

The composition of a pair of universal homeomorphisms of algebraic spaces is a
universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.53.5: The composition of a pair of universal homeomorphisms of algebraic
spaces is a universal homeomorphism. -/
@[stacks 0CFU]
instance universalHomeomorphism_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@UniversalHomeomorphism S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of universal homeomorphisms of algebraic spaces is a
universal homeomorphism. -/
instance universalHomeomorphism_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversalHomeomorphism f] [UniversalHomeomorphism g] :
    UniversalHomeomorphism (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
