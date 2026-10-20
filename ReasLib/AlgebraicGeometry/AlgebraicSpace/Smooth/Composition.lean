/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of smooth morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Smooth morphisms of algebraic spaces are stable under composition. -/
instance smooth_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Smooth S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of smooth morphisms of algebraic spaces is smooth. -/
instance smooth_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth f] [Smooth g] :
    Smooth (f ≫ g) :=
  MorphismProperty.comp_mem (@Smooth S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
