module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of proper morphisms of algebraic spaces

The composition of a pair of proper morphisms of algebraic spaces is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.40.4: A composition of proper morphisms of algebraic spaces is
proper. -/
@[stacks 04XY]
instance proper_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Proper S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of proper morphisms of algebraic spaces is proper. -/
instance proper_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Proper f] [Proper g] :
    Proper (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
