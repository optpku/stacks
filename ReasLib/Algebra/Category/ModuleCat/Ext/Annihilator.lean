/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Annihilators of Ext modules

@stack 00LV

This leaf records how annihilators of either argument act on Ext. The public
API is stated directly on the canonical `ModuleCat` Ext object.
-/

open CategoryTheory
open CategoryTheory.Abelian

universe u

namespace CategoryTheory.Abelian.Ext

variable {R M N : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- Lemma 10.71.8, tag `00LV`: an element annihilating either argument
annihilates every Ext module between them. -/
@[stacks 00LV "annihilator of either Ext argument"]
theorem mem_annihilator_of_mem_target_or_source {x : R}
    (hx : x ∈ Module.annihilator R N ∨ x ∈ Module.annihilator R M) (i : ℕ) :
    x ∈ Module.annihilator R
      (Ext (ModuleCat.of R M) (ModuleCat.of R N) i) := sorry

/-- Pointwise form of `mem_annihilator_of_mem_target_or_source`. -/
@[stacks 00LV "pointwise Ext annihilation"]
theorem smul_eq_zero_of_annihilates_target_or_source {x : R}
    (hx : (∀ n : N, x • n = 0) ∨ ∀ m : M, x • m = 0)
    (i : ℕ) (e : Ext (ModuleCat.of R M) (ModuleCat.of R N) i) :
    x • e = 0 := sorry

end CategoryTheory.Abelian.Ext
