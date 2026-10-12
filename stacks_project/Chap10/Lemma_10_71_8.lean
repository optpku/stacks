/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Ext.Annihilator
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.71.8
@stack 00LV
-/

/- Domain triage:
* primary domain: linear `Ext` groups in `ModuleCat R`;
* sampled owner declarations: `smul_eq_comp_mk₀`, `mk₀_smul`, `smul_comp`, and
  `mk₀_eq_zero_iff`;
* core/canonical owner abstraction: the `R`-module structure on `Ext` in the linear abelian
  category `ModuleCat R`, with source and target scalar actions both expressed through `mk₀`;
* source-facing layer: the annihilator statement for `Ext^i_R(M, N)`;
* primitive data: the scalar `x`, the two `R`-modules `M` and `N`, the degree `i`, and the class
  `e : Ext^i_R(M, N)`;
* derived API: target-side scalar action via `smul_eq_comp_mk₀`, source-side scalar action via
  `mk₀_smul`, `smul_comp`, and `mk₀_id_comp`, and zero detection via `mk₀_eq_zero_iff`.

This item is therefore `source-facing`: it adds a textbook annihilator statement about the
canonical owner object `Ext`, so the refinement is to consume the owner linearity API directly
rather than routing through a parallel resolution-level public wrapper. -/

/- Lemma 10.71.8: if `x : R` annihilates either `N` or `M`, then it annihilates the Ext module
`Ext^i_R(M, N)` for every `i`. -/
@[stacks 00LV]
#check @CategoryTheory.Abelian.Ext.mem_annihilator_of_mem_target_or_source

@[stacks 00LV "pointwise form"]
#check @CategoryTheory.Abelian.Ext.smul_eq_zero_of_annihilates_target_or_source

@[stacks 00LV "target scalar action on Ext"]
#check @CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀

@[stacks 00LV "source scalar action on Ext"]
#check @CategoryTheory.Abelian.Ext.mk₀_smul

@[stacks 00LV "scalar action and Ext composition"]
#check @CategoryTheory.Abelian.Ext.smul_comp
