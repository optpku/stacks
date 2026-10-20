/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.Algebra.Module.IdealPower.Predicate
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bijective base change on ideal-power torsion modules

The main theorem upgrades compatible isomorphisms on all positive ideal-power
quotients to bijectivity of the canonical tensor unit on every ideal-power
torsion module.  The library-facing tensor orientation is `R' ⊗[R] M`; tensor
symmetry identifies it with the source's `M ⊗[R] R'`.

@stack 0BNK
-/

@[expose] public section

open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]
variable {R' : Type v} [CommRing R'] [Algebra R R']
variable (I : Ideal R)
variable {M : Type w} [AddCommMonoid M] [Module R M]

/-- The positive finite power-torsion stages exhaust an ideal-power torsion
module. -/
@[stacks 0BNK "finite power-torsion stages"]
theorem idealPowerTorsion_iSup_powerTorsion_eq_top
    (hM : Module.IsIdealPowerTorsion I M) :
    (⨆ n : ℕ+, Ideal.powerTorsion I M (n : ℕ)) = ⊤ := sorry
-- Proof strategy: rewrite `hM` through the elementwise positive-exponent criterion and use
-- `Submodule.iSup_eq_top` to place each element in its witnessed finite stage.

/-- The `I ^ n`-power torsion stage is annihilated by `I ^ n`. -/
@[stacks 0BNK "annihilator of a finite ideal-power torsion stage"]
theorem powerTorsion_le_annihilator (n : ℕ) :
    I ^ n ≤ Module.annihilator R (Ideal.powerTorsion I M n) := sorry
-- Proof strategy: unfold `Ideal.powerTorsion`; the defining torsion membership says every
-- element of the stage is killed by every scalar in `I ^ n`.

/-- An ideal contained in a module annihilator acts trivially on the whole
module. -/
@[stacks 0BNK "annihilator criterion for trivial ideal action"]
theorem smul_top_eq_bot_of_le_annihilator
    {T : Type w} [AddCommMonoid T] [Module R T]
    (J : Ideal R) (hJann : J ≤ Module.annihilator R T) :
    J • (⊤ : Submodule R T) = ⊥ := sorry
-- Proof strategy: apply `Submodule.eq_bot_iff` and expand generators of the ideal action;
-- every scalar action vanishes by `hJann`.

/-- Bijectivity of a quotient ring map implies bijectivity of its algebra-map
presentation. -/
@[stacks 0BNK "quotient-map algebra presentation"]
theorem quotientMapₐ_bijective_of_quotientMap_bijective
    (J : Ideal R)
    (hquotJ : Function.Bijective
      (Ideal.quotientMap
        (J.map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map)) :
    Function.Bijective
      (Ideal.quotientMapₐ
        (R₁ := R)
        (I := J)
        (J := J.map (algebraMap R R'))
        (f := Algebra.ofId R R')
        Ideal.le_comap_map) := sorry
-- Proof strategy: show the two quotient maps agree pointwise after forgetting the algebra
-- structure, then transport injectivity and surjectivity across that equality.

/-- If `I ^ n` annihilates a module and the corresponding quotient map is
bijective, then the canonical tensor base-change unit is bijective. -/
@[stacks 0BNK "bounded ideal-power tensor base change"]
theorem tensorBaseChange_bijective_of_annihilator_pow_le_of_quotientMapBijective
    (n : ℕ+)
    {T : Type w} [AddCommMonoid T] [Module R T]
    (hJann : I ^ (n : ℕ) ≤ Module.annihilator R T)
    (hquotn : Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map)) :
    Function.Bijective (TensorProduct.mk R R' T 1) := sorry
-- Proof strategy: regard `T` as an `R ⧸ I ^ n`-module, rewrite scalar extension through the
-- bijective quotient algebra map, and use the tensor unit isomorphism over the quotient.

/-- Lemma 15.89.9 (0BNK): if all positive ideal-power quotient maps
`R ⧸ I ^ n ⟶ R' ⧸ I ^ n R'` are bijective, then the canonical tensor unit
`M ⟶ R' ⊗[R] M` is bijective for every `I`-power torsion module `M`. -/
@[stacks 0BNK "ideal-power torsion tensor base change"]
theorem tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective
    (hM : Module.IsIdealPowerTorsion I M)
    (hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map)) :
    Function.Bijective (TensorProduct.mk R R' M 1) := sorry
-- Proof strategy: prove bijectivity on every finite stage with
-- `tensorBaseChange_bijective_of_annihilator_pow_le_of_quotientMapBijective`, express `M`
-- as their supremum, and pass injectivity and surjectivity through the directed union.

end
