/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Ext.Factorization

/-!
# Lemma 15.102.2

@stack 0G3L
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian
open Ideal.PowerSubmodule
open CategoryTheory.DerivedCategory.IdealPower
open CategoryTheory.DerivedCategory.IdealPower.ExtRestriction

noncomputable section

universe u v

-- Local instance justification (defeq pin): the source-facing check uses mathlib's canonical
-- derived-category model for every Ext group in the displayed factorization.
attribute [local instance] CategoryTheory.HasExt.standard

/-
Lemma 15.102.2 (0G3L): let `A` be a Noetherian ring, let `I` be an ideal of `A`, let `M` be a
finite `A`-module, and let `N` be any `A`-module.  For every `p > 0`, there is a cutoff `c` such
that, whenever `n ≥ c`, restriction

`Ext M N p ⟶ Ext (I ^ n M) N p`

factors through

`Ext (I ^ n M) (I ^ (n - c) N) p`.

The reusable owner is universe-polymorphic, represents the commuting triangle by an equality of
linear maps, supplies an explicit degree-zero factor, and also records the stronger cutoff that is
uniform in the target module.  This file is only the exact source-facing recall boundary.
-/

/- Canonical factorization data and the two reusable existence predicates. -/
@[stacks 0G3L "adic Ext factorization data"]
#check @Factorisation
@[stacks 0G3L "adic Ext factorization at one stage"]
#check @FactorsAt
@[stacks 0G3L "eventual adic Ext factorization"]
#check @EventuallyFactors
@[stacks 0G3L "pointwise adic Ext factorization equation"]
#check @Factorisation.fac_apply

/- Concrete degree zero and uniform Noetherian existence. -/
@[stacks 0G3L "degree-zero adic Ext factorization"]
#check @Factorisation.degreeZero
@[stacks 0G3L "uniform positive-degree adic Ext factorization"]
#check @existsEventuallyFactors_succ
@[stacks 0G3L "uniform all-degree adic Ext factorization"]
#check @existsEventuallyFactors

section SourceStatement

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A) (M N : ModuleCat.{v} A) [Module.Finite A M]
variable (p : ℕ) (hp : 0 < p)

@[stacks 0G3L "Lemma 15.102.2"]
#check (existsFactorisation_of_pos I M N p hp :
  ∃ c : ℕ, ∀ n ≥ c,
    ∃ φ : Ext M N p →ₗ[A] Ext (stageObj I M n) (stageObj I N (n - c)) p,
      ∀ x : Ext M N p,
        subtypeExtPostcomp I (stageObj I M n) N (n - c) p (φ x) =
          subtypeExtPrecomp I M N n p x)

end SourceStatement
