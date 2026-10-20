/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Countable.Basic
public import Mathlib.Data.Set.Countable
public import ReasLib.RingTheory.Flatness.MittagLeffler.PowerSeries
import StacksCheckRecall

@[expose] public section

/-!
# Remark 10.93.2

@stack 059Y

The `ℤ`-module `ℤ⟦X⟧` is flat and Mittag--Leffler but not projective. The obstruction is the
source's explicit submodule of power series whose coefficients are eventually divisible by every
power of a fixed prime.
-/

namespace Module

open scoped PowerSeries

/-- A formal power series over `ℤ` has an eventually `p`-adically divisible tail when, for every
positive exponent, only finitely many coefficients fail to be divisible by that power of `p`. -/
def HasPAdicallyDivisibleTail (p : ℕ) (f : ℤ⟦X⟧) : Prop :=
  ∀ m : ℕ, Set.Finite {i : ℕ | ¬ ((p : ℤ) ^ (m + 1) ∣ PowerSeries.coeff i f)}

/-- The zero power series has an eventually `p`-adically divisible tail. -/
theorem hasPAdicallyDivisibleTail_zero (p : ℕ) :
    HasPAdicallyDivisibleTail p (0 : ℤ⟦X⟧) := sorry

/-- Eventually `p`-adically divisible tails are closed under addition. -/
theorem hasPAdicallyDivisibleTail_add (p : ℕ) {f g : ℤ⟦X⟧}
    (hf : HasPAdicallyDivisibleTail p f) (hg : HasPAdicallyDivisibleTail p g) :
    HasPAdicallyDivisibleTail p (f + g) := sorry

/-- Eventually `p`-adically divisible tails are closed under integer scalar multiplication. -/
theorem hasPAdicallyDivisibleTail_smul (p : ℕ) (n : ℤ) {f : ℤ⟦X⟧}
    (hf : HasPAdicallyDivisibleTail p f) :
    HasPAdicallyDivisibleTail p (n • f) := sorry

/-- The power series whose coefficients have eventually `p`-adically divisible tails form a
concrete `ℤ`-submodule of `ℤ⟦X⟧`. -/
@[stacks 059Y "divisible-tail submodule"]
def pAdicallyDivisibleTailSubmodule (p : ℕ) : Submodule ℤ ℤ⟦X⟧ where
  carrier := {f | HasPAdicallyDivisibleTail p f}
  zero_mem' := hasPAdicallyDivisibleTail_zero p
  add_mem' := fun hf hg ↦ hasPAdicallyDivisibleTail_add p hf hg
  smul_mem' := fun n _ hf ↦ hasPAdicallyDivisibleTail_smul p n hf

/-- Membership in `pAdicallyDivisibleTailSubmodule p` is exactly the eventual coefficientwise
divisibility condition. -/
@[simp]
theorem mem_pAdicallyDivisibleTailSubmodule_iff (p : ℕ) (f : ℤ⟦X⟧) :
    f ∈ pAdicallyDivisibleTailSubmodule p ↔ HasPAdicallyDivisibleTail p f := sorry

/- Remark 10.93.2 (1): integer power series are flat over `ℤ`. -/
@[stacks 059Y "(1), flatness"]
#check PowerSeries.intFlat

/- Remark 10.93.2 (2): integer power series are Mittag--Leffler over `ℤ`. -/
@[stacks 059Y "(2), Mittag-Leffler"]
#check PowerSeries.intMittagLeffler

/-- For a prime `p`, the divisible-tail submodule is uncountable. -/
theorem tailSubmodule_uncountable {p : ℕ} (hp : Nat.Prime p) :
    Uncountable (pAdicallyDivisibleTailSubmodule p) := sorry

/-- The quotient of the divisible-tail submodule by its `p`-multiples is countable. -/
theorem tailModPQuotient_countable {p : ℕ} (hp : Nat.Prime p) :
    Countable
      ((pAdicallyDivisibleTailSubmodule p) ⧸
        ((Ideal.span ({(p : ℤ)} : Set ℤ)) • ⊤ :
          Submodule ℤ (pAdicallyDivisibleTailSubmodule p))) := sorry

/-- The divisible-tail submodule is not a free abelian group. -/
theorem pAdicallyDivisibleTailSubmodule_not_free {p : ℕ} (hp : Nat.Prime p) :
    ¬ Module.Free ℤ (pAdicallyDivisibleTailSubmodule p) := sorry

/-- Remark 10.93.2 (3): the `ℤ`-module `ℤ⟦X⟧` is not projective. -/
@[stacks 059Y "(3), nonprojectivity"]
theorem integerPowerSeries_not_projective :
    ¬ Module.Projective ℤ ℤ⟦X⟧ := sorry

end Module

#print axioms Module.pAdicallyDivisibleTailSubmodule
