/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideal Contraction Along Algebraic Maps

@stack 0H7L
-/

@[expose] public section

universe u v

namespace Algebra.IsAlgebraic

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [Algebra R S] [IsDomain S]

/-- A nonzero ideal contracts nontrivially along an algebraic map into a domain. -/
@[stacks 0H7L "nonzero ideals contract nontrivially along algebraic maps"]
theorem comap_ne_bot (h : Algebra.IsAlgebraic R S)
    (I : Ideal S) (hI : I ≠ ⊥) :
    I.comap (algebraMap R S) ≠ ⊥ := by
  obtain ⟨x, hxI, hx0⟩ := (Submodule.ne_bot_iff I).mp hI
  exact Ideal.comap_ne_bot_of_algebraic_mem hx0 hxI (h.isAlgebraic x)

/-- An ideal with zero contraction along an algebraic map into a domain is zero. -/
@[stacks 0H7L "zero contraction along an algebraic map"]
theorem eq_bot_of_comap_eq_bot (h : Algebra.IsAlgebraic R S)
    (I : Ideal S) (hI : I.comap (algebraMap R S) = ⊥) :
    I = ⊥ := by
  by_contra hne
  exact h.comap_ne_bot I hne hI

end Algebra.IsAlgebraic
