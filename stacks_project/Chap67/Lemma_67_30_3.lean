/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of flat morphisms of algebraic spaces

The composition of a pair of flat morphisms of algebraic spaces is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.30.3: The composition of flat morphisms is flat. -/
@[stacks 03MN]
instance flat_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Flat S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of flat morphisms of algebraic spaces is flat. -/
instance flat_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    Flat (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
