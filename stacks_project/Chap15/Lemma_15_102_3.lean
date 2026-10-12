/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Ext.Vanishing

/-!
# Lemma 15.102.3

@stack 0927
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.DerivedCategory.IdealPower
open CategoryTheory.DerivedCategory.IdealPower.ExtRestriction

noncomputable section

universe u v

-- Local instance justification (defeq pin): the source-facing statement uses mathlib's canonical
-- derived-category model for Ext.
attribute [local instance] CategoryTheory.HasExt.standard

/-
Lemma 15.102.3 (0927): let `A` be Noetherian, let `M` be a finite `A`-module, and suppose one
power of `I` annihilates `N`.  For each `p > 0`, restriction along `I ^ n M ⟶ M` is zero for some
`n`:

`Ext M N p ⟶ Ext (I ^ n M) N p`.

The shared owner distinguishes uniform annihilation from elementwise ideal-power torsion.  It also
records the stronger conclusion that the restriction maps vanish at every sufficiently large
stage, in every Ext degree, with a cutoff uniform among targets killed by the same exponent.
-/

@[stacks 0927 "module annihilated by an ideal power"]
#check @Module.IsAnnihilatedByPower
@[stacks 0927 "eventual vanishing of adic Ext restriction"]
#check @EventuallyZero
@[stacks 0927 "uniform vanishing cutoff for adic Ext restriction"]
#check @existsUniformZeroCutoff
@[stacks 0927 "adic Ext vanishing for a power-annihilated target"]
#check @eventuallyZero_of_isAnnihilatedByPower

section SourceStatement

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A) (M N : ModuleCat.{v} A) [Module.Finite A M]
variable (p : ℕ) (hp : 0 < p) (hN : Module.IsAnnihilatedByPower I N)

@[stacks 0927 "Lemma 15.102.3"]
#check (existsZero_of_pos I M N p hp hN :
  ∃ n : ℕ, subtypeExtPrecomp I M N n p = 0)

end SourceStatement
