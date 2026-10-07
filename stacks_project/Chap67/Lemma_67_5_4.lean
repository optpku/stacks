module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of surjective morphisms of algebraic spaces

The composition of a pair of surjective morphisms of algebraic spaces is
surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.5.4: The composition of surjective morphisms is surjective. -/
@[stacks 03MG]
instance surjective_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Surjective S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of surjective morphisms of algebraic spaces is surjective. -/
instance surjective_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [Surjective g] :
    Surjective (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
