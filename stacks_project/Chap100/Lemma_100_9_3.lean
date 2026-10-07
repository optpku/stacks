module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap100.Definition_100_9_1_Immersion

/-!
# Composition of immersions of algebraic stacks

A composition of immersions, closed immersions, or open immersions of algebraic
stacks is again an immersion, closed immersion, or open immersion respectively.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace Immersion

/-- Lemma 100.9.3 (1): compositions of immersions of algebraic stacks are
immersions. -/
@[stacks 0502]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y)
    (g : Y ⟶ Z) [Immersion f] [Immersion g] : Immersion (f ≫ g) := sorry

end Immersion

namespace ClosedImmersion

/-- Lemma 100.9.3 (2): compositions of closed immersions of algebraic stacks are
closed immersions. -/
@[stacks 0502]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y)
    (g : Y ⟶ Z) [ClosedImmersion f] [ClosedImmersion g] :
    ClosedImmersion (f ≫ g) := sorry

end ClosedImmersion

namespace OpenImmersion

/-- Lemma 100.9.3 (3): compositions of open immersions of algebraic stacks are
open immersions. -/
@[stacks 0502]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y)
    (g : Y ⟶ Z) [OpenImmersion f] [OpenImmersion g] :
    OpenImmersion (f ≫ g) := sorry

end OpenImmersion

/-- Immersions of groupoid fibrations over `S` are stable under composition as a
morphism property. -/
instance isImmersion_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Immersion S : MorphismProperty (GroupoidsOver S)) := sorry

/-- Closed immersions of groupoid fibrations over `S` are stable under
composition as a morphism property. -/
instance isClosedImmersion_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@ClosedImmersion S : MorphismProperty (GroupoidsOver S)) := sorry

/-- Open immersions of groupoid fibrations over `S` are stable under composition
as a morphism property. -/
instance isOpenImmersion_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@OpenImmersion S : MorphismProperty (GroupoidsOver S)) := sorry

end AlgebraicGeometry.Groupoids.Hom
