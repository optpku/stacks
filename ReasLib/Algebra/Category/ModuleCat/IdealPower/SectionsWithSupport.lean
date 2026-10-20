/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.IdealPower.Torsion

/-!
# Sections with support in an ideal

The primary-component coreflector followed by inclusion is the underived functor of sections
supported on the zero locus of an ideal.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ModuleCat.IdealPowerTorsion

variable {A : Type u} [CommRing A]

/-- Sections supported on the zero locus of `I`, viewed as an endofunctor of `A`-modules. -/
noncomputable abbrev sectionsWithSupport (I : Ideal A) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  coreflector I ⋙ inclusion I

/-- The module underlying sections with support is the primary component of the module. -/
theorem sectionsWithSupport_obj (I : Ideal A) (M : ModuleCat A) :
    (sectionsWithSupport I).obj M = ModuleCat.of A (I.primaryComponent M) := sorry

/-- Sections with support form an additive functor. -/
instance sectionsWithSupportAdditive (I : Ideal A) :
    (sectionsWithSupport I).Additive := sorry

/-- Sections with support preserve finite limits. -/
instance sectionsWithSupportPreservesFiniteLimits (I : Ideal A) :
    PreservesFiniteLimits (sectionsWithSupport I) := sorry

end CategoryTheory.ModuleCat.IdealPowerTorsion
