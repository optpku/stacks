/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of open morphisms of algebraic spaces

Open morphisms of algebraic spaces are stable under composition, as are
universally open morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Open morphisms of algebraic spaces are stable under composition. -/
instance open_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Open S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of open morphisms of algebraic spaces is open. -/
instance open_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Open f] [Open g] :
    Open (f ≫ g) :=
  MorphismProperty.comp_mem (@Open S) f g inferInstance inferInstance

/-- Universally open morphisms of algebraic spaces are stable under composition. -/
instance universallyOpen_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@UniversallyOpen S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of universally open morphisms of algebraic spaces is
universally open. -/
instance universallyOpen_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyOpen f] [UniversallyOpen g] :
    UniversallyOpen (f ≫ g) :=
  MorphismProperty.comp_mem (@UniversallyOpen S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
