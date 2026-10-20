/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Support
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Support and ideal powers

This leaf owns the finite-generation criterion relating module support to an ideal's zero locus.
The annihilator formulation is primary because it is independent of a chosen presentation of the
module; the pointwise `(I ^ n) • ⊤ = ⊥` form is the pointwise companion.
-/

@[expose] public section

universe u v

open PrimeSpectrum

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- For a finite module and a finitely generated ideal, support is contained in the ideal's zero
locus exactly when one power of the ideal is contained in the module annihilator. The statement is
parameterized by an arbitrary ideal, so list-generated ideals are only a downstream
specialization. -/
@[stacks 00L6 "support containment and an annihilating ideal power"]
theorem exists_pow_le_annihilator_iff_support_subset_zeroLocus
    (I : Ideal R) (hI : I.FG) :
    (∃ n : ℕ, I ^ n ≤ annihilator R M) ↔ support R M ⊆ zeroLocus I := sorry

/-- The same support criterion expressed as vanishing of an ideal-power action on the top
submodule. This is a companion rather than the data owner, since the annihilator form composes
directly with support and radical APIs. -/
@[stacks 00L6 "support containment and an annihilating ideal action"]
theorem exists_pow_smul_top_eq_bot_iff_support_subset_zeroLocus
    (I : Ideal R) (hI : I.FG) :
    (∃ n : ℕ, (I ^ n) • (⊤ : Submodule R M) = ⊥) ↔ support R M ⊆ zeroLocus I := sorry

end Module

end
