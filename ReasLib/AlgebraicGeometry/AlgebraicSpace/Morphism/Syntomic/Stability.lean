module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of syntomic morphisms of algebraic spaces

Syntomic morphisms of algebraic spaces are stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Syntomic morphisms of algebraic spaces are stable under composition. -/
instance syntomic_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Syntomic S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of syntomic morphisms of algebraic spaces is syntomic. -/
instance syntomic_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Syntomic f] [Syntomic g] :
    Syntomic (f ≫ g) :=
  MorphismProperty.comp_mem (@Syntomic S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
