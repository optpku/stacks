module

import StacksCheckRecall
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import ReasLib.CategoryTheory.Abelian.Injective.Ext

/-!
# Lemma 15.55.3

@stack 0AVE
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Abelian.Ext

universe u

/- Lemma 15.55.3 (0AVE): an `R`-module is injective if and only if every degree-one extension
into it vanishes. -/
@[stacks 0AVE "injective modules and vanishing Ext one"]
#check fun (R : Type u) [Ring R] (J : ModuleCat.{u} R) ↦
  (injective_iff_ext_one_eq_zero J :
    Injective J ↔ ∀ M : ModuleCat R, ∀ e : Ext M J 1, e = 0)

#check @injective_iff_subsingleton_ext_one
#check @CategoryTheory.injective_tfae
