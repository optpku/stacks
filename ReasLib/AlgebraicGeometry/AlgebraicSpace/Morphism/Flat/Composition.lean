module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of flat morphisms of algebraic spaces

The composition of a pair of flat morphisms of algebraic spaces is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The composition of flat morphisms of algebraic spaces is flat. -/
instance flat_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] :
    Flat (f ≫ g) := sorry

/-- Flatness of morphisms of algebraic spaces is stable under composition. -/
instance flat_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Flat S : MorphismProperty (AlgebraicSpace S)) where
  comp_mem f g := @flat_comp S _ _ _ f g

end AlgebraicGeometry.AlgebraicSpace
