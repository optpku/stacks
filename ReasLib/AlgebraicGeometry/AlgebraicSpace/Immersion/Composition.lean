/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of immersions of algebraic spaces

Immersions, closed immersions, and open immersions of algebraic spaces over a
scheme are stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A composition of immersions of algebraic spaces over a scheme is an immersion. -/
instance IsImmersion.comp {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    (f : F ⟶ G) (g : G ⟶ H) [IsImmersion f] [IsImmersion g] : IsImmersion (f ≫ g) :=
  sorry

/-- A composition of closed immersions of algebraic spaces over a scheme is a closed
immersion. -/
instance IsClosedImmersion.comp {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    (f : F ⟶ G) (g : G ⟶ H) [IsClosedImmersion f] [IsClosedImmersion g] :
    IsClosedImmersion (f ≫ g) :=
  sorry

/-- A composition of open immersions of algebraic spaces over a scheme is an open immersion. -/
instance IsOpenImmersion.comp {S : Scheme.{u}} {F G H : AlgebraicSpace S}
    (f : F ⟶ G) (g : G ⟶ H) [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (f ≫ g) :=
  sorry

/-- Immersions of algebraic spaces over `S` are stable under composition as a morphism
property. -/
instance isImmersion_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@IsImmersion S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- Closed immersions of algebraic spaces over `S` are stable under composition as a morphism
property. -/
instance isClosedImmersion_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- Open immersions of algebraic spaces over `S` are stable under composition as a morphism
property. -/
instance isOpenImmersion_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@IsOpenImmersion S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
