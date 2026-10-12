/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective modules from ideal-quotient extension groups

This is the module-category specialization of the categorical degree-one Ext criterion.  The
ideal-quotient test family is kept here, alongside Baer's criterion, rather than in the generic
abelian-category API.
@stack 0AVF
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian

universe u

namespace CategoryTheory.ModuleCat

variable {R : Type u} [Ring R]

/-- An `R`-module is injective exactly when its degree-one Ext group from every ideal quotient is
subsingleton. -/
@[stacks 0AVF "ideal-quotient Ext criterion"]
theorem injective_iff_idealQuotient_ext_one (J : ModuleCat R) :
    Injective J ↔
      ∀ I : Ideal R, Subsingleton (Ext (ModuleCat.of R (R ⧸ I)) J 1) := sorry

/-- Lemma 15.55.4, Stacks `0AVF`: injectivity, vanishing of degree-one Ext from all ideal
quotients, and Baer's extension criterion are equivalent. -/
@[stacks 0AVF "Baer criterion"]
theorem injective_idealQuotient_ext_tfae (J : ModuleCat R) :
    List.TFAE [
      Injective J,
      ∀ I : Ideal R, ∀ e : Ext (ModuleCat.of R (R ⧸ I)) J 1, e = 0,
      Module.Baer R J
    ] := sorry

end CategoryTheory.ModuleCat
