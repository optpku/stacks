/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Segre
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of projective scheme morphisms

This file collects the composition APIs for projective, H-projective, and locally projective
morphisms.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Projective morphisms are stable under composition. -/
instance projective_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @Projective := sorry

/-- The composite of two projective morphisms is projective. -/
theorem Projective.comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Projective f) (hg : Projective g) :
    Projective (f ≫ g) := sorry

/-- Typeclass form of closure of projective morphisms under composition. -/
instance projective_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Projective f] [Projective g] :
    Projective (f ≫ g) := sorry

/-- H-projective morphisms are stable under composition. -/
instance hProjective_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @HProjective := sorry

/-- The composite of two H-projective morphisms is H-projective. -/
theorem HProjective.comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : HProjective f) (hg : HProjective g) :
    HProjective (f ≫ g) := sorry

/-- Typeclass form of closure of H-projective morphisms under composition. -/
@[stacks 01WE, instance]
theorem hProjective_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HProjective f] [HProjective g] :
    HProjective (f ≫ g) := sorry

/-- Locally projective morphisms are stable under composition. -/
instance locallyProjective_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @LocallyProjective := sorry

/-- The composite of two locally projective morphisms is locally projective. -/
theorem LocallyProjective.comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : LocallyProjective f) (hg : LocallyProjective g) :
    LocallyProjective (f ≫ g) := sorry

/-- Typeclass form of closure of locally projective morphisms under composition. -/
instance locallyProjective_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyProjective f] [LocallyProjective g] :
    LocallyProjective (f ≫ g) := sorry

namespace Projective

/-- A closed immersion followed by a projective morphism is projective. -/
theorem comp_of_isClosedImmersion
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    (hf : IsClosedImmersion f) [Projective g] :
    Projective (f ≫ g) := sorry

end Projective

end AlgebraicGeometry
