/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism

/-!
# Composition of monomorphisms of groupoid fibrations

Monomorphisms of groupoid fibrations are stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom.Mono

/-- Monomorphisms of groupoid fibrations are stable under composition. -/
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Mono S : MorphismProperty (GroupoidsOver S)) := sorry

/-- The composition of monomorphisms of groupoid fibrations is a
monomorphism. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [hf : Mono f] [hg : Mono g] : Mono (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g hf hg

end AlgebraicGeometry.Groupoids.Hom.Mono
