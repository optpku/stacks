/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Tactic.CrossRefAttribute

/-!
# Heights of primes over principal ideals

@stack 00KV
@stack 031T
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

namespace IsPrincipal

/-- A prime minimal over a principal ideal has height at most one.  The principal-ideal proof is
an ordinary argument so callers need not install a local instance. -/
@[stacks 00KV "height bound for a minimal prime over a principal ideal"]
theorem height_le_one_of_mem_minimalPrimes
    {I p : Ideal R} (hI : I.IsPrincipal) (hp : p ∈ I.minimalPrimes) :
    p.height ≤ 1 := by
  obtain ⟨x, rfl⟩ := hI
  exact height_le_one_of_isPrincipal_of_mem_minimalPrimes (span {x}) p hp

end IsPrincipal

variable [IsDomain R]

/-- A prime minimal over a nonzero principal ideal in a Noetherian domain has height one. -/
@[stacks 031T "height of a minimal prime over a nonzero principal ideal"]
theorem height_eq_one_of_isPrincipal_of_mem_minimalPrimes
    (I : Ideal R) [I.IsPrincipal] (hI : I ≠ ⊥)
    (p : Ideal R) (hp : p ∈ I.minimalPrimes) :
    p.height = 1 := by
  apply le_antisymm
  · exact IsPrincipal.height_le_one_of_mem_minimalPrimes inferInstance hp
  · rw [Order.one_le_iff_ne_zero]
    intro hp_zero
    have hp_bot : p = ⊥ := height_eq_zero_iff_eq_bot.mp hp_zero
    exact hI (bot_unique (hp.1.2.trans_eq hp_bot))

end Ideal
