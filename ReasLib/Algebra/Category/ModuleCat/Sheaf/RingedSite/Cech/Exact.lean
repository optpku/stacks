/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness of ringed-site Cech complexes

The coefficient category in this file is the category of presheaf modules. Evaluation and
restriction of scalars are exact there, so the Cech complex functor is exact. This is not an
exactness statement for the forgetful functor from module sheaves to module presheaves.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Restricted sections on a slice form an additive functor of presheaf modules. -/
instance sectionsOnOverAdditive
    (𝒪 : Sheaf J RingCat.{w}) (U : C) :
    (sectionsOnOver 𝒪 U).Additive := sorry

/-- The restricted-sections functor from presheaf modules to module-valued presheaves on a
slice is exact. -/
@[stacks 01EJ "exactness of restricted sections on a slice"]
theorem sectionsOnOver_exact
    (𝒪 : Sheaf J RingCat.{w}) (U : C) :
    exactFunctor (PresheafOfModules.{w} 𝒪.obj)
      ((Over U)ᵒᵖ ⥤ ModuleCat.{w} (𝒪.obj.obj (op U)))
      (sectionsOnOver 𝒪 U) := sorry

/-- The ringed-site Cech complex is additive in its presheaf-module coefficients. -/
instance cechComplexAdditive
    (𝒪 : Sheaf J RingCat.{w}) (U : C) [HasFiniteProducts (Over U)]
    {ι : Type w} (family : ι → Over U) :
    (cechComplex 𝒪 U family).Additive := sorry

/-- Lemma 20.10.1 (Tag 01EJ): for a family in `Over U`, the ringed-site Cech complex functor on
presheaf modules is exact. -/
@[stacks 01EJ "exact ringed-site module Cech complex"]
theorem cechComplex_exact
    (𝒪 : Sheaf J RingCat.{w}) (U : C) [HasFiniteProducts (Over U)]
    {ι : Type w} (family : ι → Over U) :
    exactFunctor (PresheafOfModules.{w} 𝒪.obj)
      (CochainComplex (ModuleCat.{w} (𝒪.obj.obj (op U))) ℕ)
      (cechComplex 𝒪 U family) := sorry

end SheafOfModules.RingedSite
