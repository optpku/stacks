/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of locally of finite presentation morphisms of algebraic spaces

Morphisms of algebraic spaces that are locally of finite presentation are stable
under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Locally of finite presentation morphisms of algebraic spaces are stable under
composition. -/
instance locallyOfFinitePresentation_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- The composition of locally of finite presentation morphisms of algebraic
spaces is locally of finite presentation. -/
instance locallyOfFinitePresentation_comp {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation (f ≫ g) :=
  MorphismProperty.comp_mem (@LocallyOfFinitePresentation S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
