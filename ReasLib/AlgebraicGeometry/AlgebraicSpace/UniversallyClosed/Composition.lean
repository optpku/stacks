module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed

/-!
# Composition of closed morphisms of algebraic spaces

Closed morphisms and universally closed morphisms of algebraic spaces are stable
under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Closed morphisms of algebraic spaces are stable under composition. -/
instance closed_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Closed S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of closed morphisms of algebraic spaces is closed. -/
instance closed_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Closed f] [Closed g] :
    Closed (f ≫ g) :=
  MorphismProperty.comp_mem (@Closed S) f g inferInstance inferInstance

/-- Universally closed morphisms of algebraic spaces are stable under composition. -/
instance universallyClosed_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@UniversallyClosed S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of universally closed morphisms of algebraic spaces is
universally closed. -/
instance universallyClosed_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyClosed f] [UniversallyClosed g] :
    UniversallyClosed (f ≫ g) :=
  MorphismProperty.comp_mem (@UniversallyClosed S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
