/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

/-!
# Composition of immersions of groupoid fibrations

Immersions, closed immersions, and open immersions of groupoid fibrations over
a scheme are stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace Immersion

/-- A composition of immersions of groupoid fibrations is an immersion. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y)
    (g : Y ⟶ Z) [Immersion f] [Immersion g] : Immersion (f ≫ g) := sorry

end Immersion

namespace ClosedImmersion

/-- A composition of closed immersions of groupoid fibrations is a closed immersion. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y)
    (g : Y ⟶ Z) [ClosedImmersion f] [ClosedImmersion g] :
    ClosedImmersion (f ≫ g) := sorry

end ClosedImmersion

namespace OpenImmersion

/-- A composition of open immersions of groupoid fibrations is an open immersion. -/
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
