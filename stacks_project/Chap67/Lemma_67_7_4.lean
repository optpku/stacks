module

public import stacks_project.Chap67.Definition_67_7_2_Submersive
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of submersive morphisms of algebraic spaces

The composition of a pair of submersive morphisms of algebraic spaces is
submersive, and the composition of a pair of universally submersive morphisms
of algebraic spaces is universally submersive.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.7.4 (1): The composition of a pair of submersive morphisms of algebraic
spaces is submersive. -/
@[stacks 0CFS]
instance submersive_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Submersive S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of submersive morphisms of algebraic spaces is submersive. -/
instance submersive_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Submersive f] [Submersive g] :
    Submersive (f ≫ g) := sorry

/-- Lemma 67.7.4 (2): The composition of a pair of universally submersive morphisms
of algebraic spaces is universally submersive. -/
@[stacks 0CFS]
instance universallySubmersive_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@UniversallySubmersive S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of universally submersive morphisms of algebraic spaces is
universally submersive. -/
instance universallySubmersive_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallySubmersive f] [UniversallySubmersive g] :
    UniversallySubmersive (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
