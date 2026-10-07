module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Ext.Factorization
public import ReasLib.Algebra.Module.IdealPower.Predicate
import Mathlib.Tactic.CrossRefAttribute

/-!
# Eventual vanishing of adic Ext restriction

An Ext restriction that factors through a sufficiently deep target stage vanishes when one power
of the ideal annihilates the target.  The strongest statement below chooses the cutoff uniformly
among all targets annihilated by the same power.

@stack 0927
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian
open Ideal.PowerSubmodule

noncomputable section

universe u v

namespace CategoryTheory.DerivedCategory.IdealPower.ExtRestriction

variable {A : Type u} [CommRing A] [HasExt (ModuleCat.{v} A)]

/-- The Ext restriction maps from the adic stages of the source are eventually zero. -/
@[stacks 0927 "eventual vanishing of adic Ext restriction"]
def EventuallyZero (I : Ideal A) (M N : ModuleCat.{v} A) (p : ℕ) : Prop :=
  ∃ c : ℕ, ∀ n, c ≤ n → subtypeExtPrecomp I M N n p = 0

/-- If a target adic stage is zero, postcomposition from that stage is the zero Ext map. -/
@[stacks 0927 "Ext postcomposition from a zero adic stage"]
theorem subtypeExtPostcomp_eq_zero_of_stage_eq_bot
    (I : Ideal A) (M N : ModuleCat.{v} A) (p m : ℕ)
    (hm : stage I N m = ⊥) :
    subtypeExtPostcomp I M N m p = 0 := sorry

namespace FactorsAt

/-- A single factorization through a zero target stage makes the corresponding restriction zero. -/
@[stacks 0927 "adic Ext factorization through a zero target stage"]
theorem precomp_eq_zero_of_stage_eq_bot
    {I : Ideal A} {M N : ModuleCat.{v} A} {p n m : ℕ}
    (hF : FactorsAt I M N p n m) (hm : stage I N m = ⊥) :
    subtypeExtPrecomp I M N n p = 0 := sorry

end FactorsAt

namespace EventuallyFactors

/-- An eventual factorization is zero once its target exponent passes a zero adic stage. -/
@[stacks 0927 "eventual adic Ext factorization past a zero target stage"]
theorem precomp_eq_zero_of_stage_eq_bot
    {I : Ideal A} {M N : ModuleCat.{v} A} {p c m n : ℕ}
    (hF : EventuallyFactors I M N p c) (hm : stage I N m = ⊥)
    (hn : c + m ≤ n) :
    subtypeExtPrecomp I M N n p = 0 := sorry

/-- An eventual factorization through target stages that eventually vanish is eventually zero. -/
@[stacks 0927 "eventual Ext vanishing from factorization and a zero target stage"]
theorem eventuallyZero_of_stage_eq_bot
    {I : Ideal A} {M N : ModuleCat.{v} A} {p c m : ℕ}
    (hF : EventuallyFactors I M N p c) (hm : stage I N m = ⊥) :
    EventuallyZero I M N p := sorry

/-- An eventual factorization is eventually zero when one ideal power annihilates the target. -/
@[stacks 0927 "eventual Ext vanishing from factorization and ideal-power annihilation"]
theorem eventuallyZero_of_pow_le_annihilator
    {I : Ideal A} {M N : ModuleCat.{v} A} {p c m : ℕ}
    (hF : EventuallyFactors I M N p c)
    (hm : I ^ m ≤ Module.annihilator A N) :
    EventuallyZero I M N p := sorry

/-- An eventual factorization is eventually zero for a uniformly power-annihilated target. -/
@[stacks 0927 "eventual Ext vanishing from factorization and bounded power torsion"]
theorem eventuallyZero_of_isAnnihilatedByPower
    {I : Ideal A} {M N : ModuleCat.{v} A} {p c : ℕ}
    (hF : EventuallyFactors I M N p c)
    (hN : Module.IsAnnihilatedByPower I N) :
    EventuallyZero I M N p := sorry

end EventuallyFactors

/-- For a fixed annihilating exponent, one vanishing cutoff works for every target module. -/
@[stacks 0927 "uniform vanishing cutoff for adic Ext restriction"]
theorem existsUniformZeroCutoff
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{v} A) [Module.Finite A M]
    (p m : ℕ) :
    ∃ c : ℕ, ∀ N : ModuleCat.{v} A,
      I ^ m ≤ Module.annihilator A N →
        ∀ n, c ≤ n → subtypeExtPrecomp I M N n p = 0 := sorry

/-- If one power of `I` annihilates the target, adic Ext restriction is eventually zero. -/
@[stacks 0927 "adic Ext vanishing for a power-annihilated target"]
theorem eventuallyZero_of_isAnnihilatedByPower
    [IsNoetherianRing A] (I : Ideal A) (M N : ModuleCat.{v} A) [Module.Finite A M]
    (p : ℕ) (hN : Module.IsAnnihilatedByPower I N) :
    EventuallyZero I M N p := sorry

/-- Stage-vanishing form of eventual adic Ext restriction vanishing. -/
@[stacks 0927 "adic Ext vanishing from a zero target stage"]
theorem eventuallyZero_of_stage_eq_bot
    [IsNoetherianRing A] (I : Ideal A) (M N : ModuleCat.{v} A) [Module.Finite A M]
    (p m : ℕ) (hm : stage I N m = ⊥) :
    EventuallyZero I M N p := sorry

/-- A power-annihilated target makes at least one adic Ext restriction map zero. -/
@[stacks 0927 "existence of a zero adic Ext restriction"]
theorem existsZero_of_isAnnihilatedByPower
    [IsNoetherianRing A] (I : Ideal A) (M N : ModuleCat.{v} A) [Module.Finite A M]
    (p : ℕ) (hN : Module.IsAnnihilatedByPower I N) :
    ∃ n : ℕ, subtypeExtPrecomp I M N n p = 0 := sorry

/-- Lemma 15.102.3 (0927): in positive degree, restriction to some adic stage of a finite source
vanishes when a power of the ideal annihilates the target. -/
@[stacks 0927 "Lemma 15.102.3"]
theorem existsZero_of_pos
    [IsNoetherianRing A] (I : Ideal A) (M N : ModuleCat.{v} A) [Module.Finite A M]
    (p : ℕ) (hp : 0 < p) (hN : Module.IsAnnihilatedByPower I N) :
    ∃ n : ℕ, subtypeExtPrecomp I M N n p = 0 := sorry

end CategoryTheory.DerivedCategory.IdealPower.ExtRestriction
