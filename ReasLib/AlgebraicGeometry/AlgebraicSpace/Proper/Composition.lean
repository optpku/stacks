module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of proper morphisms of algebraic spaces

The composition of a pair of proper morphisms of algebraic spaces is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Proper morphisms of algebraic spaces are stable under composition. -/
@[stacks 04XY]
instance proper_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Proper S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of proper morphisms of algebraic spaces is proper. -/
instance proper_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Proper f] [Proper g] :
    Proper (f ≫ g) :=
  MorphismProperty.comp_mem (@Proper S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
