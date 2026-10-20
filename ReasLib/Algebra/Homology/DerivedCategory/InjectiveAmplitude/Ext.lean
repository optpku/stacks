/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Category.ModuleCat.Injective.Ext
public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude.Ext
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective amplitude of derived module complexes from Ext

The all-heart-object criterion is inherited from the generic derived-category API.  This leaf adds
the module-specific reduction to the ideal quotients `R ⧸ I` and retains the exact three-clause
Stacks statement as a thin source-facing theorem.

@stack 0A5T
-/

@[expose] public section

open CategoryTheory
open scoped DerivedExt

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.InjectiveAmplitude

variable {R : Type u} [Ring R]

/-- For derived `R`-module complexes, it is enough to test injective amplitude on the ideal
quotients `R ⧸ I`. -/
@[stacks 0A5T "ideal-quotient form"]
theorem iff_idealQuotient_ext_subsingleton
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ) :
    HasInjectiveAmplitudeIn K a b ↔
      ∀ (I : Ideal R) (i : ℤ), i ∉ Set.Icc a b →
        Subsingleton
          (Ext⁽i⁾((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
            (ModuleCat.of R (R ⧸ I)), K)) := sorry

/-- Lemma 15.70.2: injective amplitude of a derived `R`-module complex is equivalent both to
vanishing of derived Ext from every module and to vanishing from all ideal quotients. -/
@[stacks 0A5T "ideal-quotient criterion"]
theorem ext_tfae (K : DerivedCategory (ModuleCat R)) (a b : ℤ) :
    List.TFAE [
      HasInjectiveAmplitudeIn K a b,
      ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc a b →
        ∀ e : Ext⁽i⁾((DerivedCategory.singleFunctor (ModuleCat R) 0).obj N, K), e = 0,
      ∀ (I : Ideal R) (i : ℤ), i ∉ Set.Icc a b →
        ∀ e : Ext⁽i⁾((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
          (ModuleCat.of R (R ⧸ I)), K), e = 0
    ] := sorry

end CategoryTheory.DerivedCategory.InjectiveAmplitude
