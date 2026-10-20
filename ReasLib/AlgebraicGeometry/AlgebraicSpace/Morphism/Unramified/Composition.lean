/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of unramified morphisms of algebraic spaces

The composition of unramified morphisms of algebraic spaces is unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Unramified morphisms of algebraic spaces are stable under composition. -/
instance unramified_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Unramified S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of unramified morphisms of algebraic spaces is unramified. -/
instance unramified_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Unramified f] [Unramified g] :
    Unramified (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
