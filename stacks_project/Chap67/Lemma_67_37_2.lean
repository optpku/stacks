/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of smooth morphisms of algebraic spaces

The composition of a pair of smooth morphisms of algebraic spaces is
smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.37.2: The composition of smooth morphisms is smooth. -/
@[stacks 03ZD]
instance smooth_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Smooth S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of smooth morphisms of algebraic spaces is smooth. -/
instance smooth_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth f] [Smooth g] :
    Smooth (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
