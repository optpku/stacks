module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth
public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallySmooth.Composition

/-!
# Composition of formally smooth morphisms of algebraic spaces

Formal smoothness of algebraic-space morphisms is stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FormallySmooth

/-- A composite of formally smooth morphisms of algebraic spaces is formally smooth. -/
instance comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [FormallySmooth f] [FormallySmooth g] :
    FormallySmooth (f ≫ g) :=
  sorry

/-- Formal smoothness of algebraic-space morphisms is stable under composition. -/
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FormallySmooth S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end FormallySmooth

end AlgebraicGeometry.AlgebraicSpace
