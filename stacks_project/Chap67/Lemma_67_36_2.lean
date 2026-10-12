/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_36_4_Syntomic
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of syntomic morphisms of algebraic spaces

The composition of a pair of syntomic morphisms of algebraic spaces is
syntomic.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.36.2: The composition of syntomic morphisms is syntomic. -/
@[stacks 03Z8]
instance syntomic_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Syntomic S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of syntomic morphisms of algebraic spaces is syntomic. -/
instance syntomic_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Syntomic f] [Syntomic g] :
    Syntomic (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
