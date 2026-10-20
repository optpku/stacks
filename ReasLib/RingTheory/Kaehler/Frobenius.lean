/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Frobenius criteria for Kähler differentials

@stack 031W

This leaf records characteristic-`p` field-theoretic criteria for the kernel
of the universal Kähler derivation.
-/

@[expose] public section

namespace KaehlerDifferential.Frobenius

universe u v

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {p : ℕ} [PerfectField k] [Fact p.Prime] [CharP k p]

/-- Lemma 10.158.2, tag `031W`: over a perfect field of characteristic
`p > 0`, an element of a field extension has zero universal Kähler
differential exactly when it is a `p`th power. -/
@[stacks 031W]
theorem d_eq_zero_iff_exists_pth_root (a : K) :
    KaehlerDifferential.D k K a = 0 ↔ ∃ b : K, b ^ p = a := sorry

end KaehlerDifferential.Frobenius
