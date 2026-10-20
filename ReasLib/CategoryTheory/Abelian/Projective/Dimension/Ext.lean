/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ext characterizations of projective-dimension bounds

This leaf presents the Ext-vanishing formulations of Mathlib's canonical
`HasProjectiveDimensionLE` predicate.  The statements are formulated in an arbitrary abelian
category; module-category results are direct specializations.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.HasProjectiveDimensionLE

open CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- A projective-dimension bound is equivalent to vanishing of every Ext group strictly above
the bound. -/
@[stacks 065R "higher Ext vanishing"]
theorem iff_ext_eq_zero_of_ge (X : C) (n : ℕ) :
    HasProjectiveDimensionLE X n ↔
      ∀ (Y : C) (i : ℕ), n + 1 ≤ i → ∀ e : Ext X Y i, e = 0 := sorry

/-- In a category with enough injectives, a projective-dimension bound is detected by the single
Ext degree immediately above the bound. -/
@[stacks 065R "single-degree Ext vanishing"]
theorem iff_ext_eq_zero_at_succ [EnoughInjectives C] (X : C) (n : ℕ) :
    HasProjectiveDimensionLE X n ↔
      ∀ Y : C, ∀ e : Ext X Y (n + 1), e = 0 := sorry

/-- The two Ext-vanishing formulations and the projective-dimension bound form one reusable TFAE.

The first clause is the uniform higher-degree formulation, while the second is its
single-degree detection under `EnoughInjectives`. -/
@[stacks 065R "Ext-vanishing TFAE"]
theorem ext_vanishing_tfae [EnoughInjectives C] (X : C) (n : ℕ) :
    List.TFAE [
      HasProjectiveDimensionLE X n,
      ∀ (Y : C) (i : ℕ), n + 1 ≤ i → ∀ e : Ext X Y i, e = 0,
      ∀ Y : C, ∀ e : Ext X Y (n + 1), e = 0
    ] := sorry

end CategoryTheory.HasProjectiveDimensionLE
