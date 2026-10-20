/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra

@[expose] public section

/-!
# Finite-stage evaluation of adic completions

This leaf records the compatibility between the canonical finite-stage maps of
an adic completion and the transition maps between quotient rings. It is
independent of locality, a chosen completion map, or a presentation.
-/

namespace AdicCompletion

universe u

variable {R : Type u} [CommRing R]

/-- The quotient transition after stage-`n` evaluation is stage-`m` evaluation. -/
@[simp]
theorem factorPow_comp_evalₐ (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow I h).comp (evalₐ I n).toRingHom =
      (evalₐ I m).toRingHom := sorry

/-- The pointwise form of `factorPow_comp_evalₐ`. -/
@[simp]
theorem factorPow_evalₐ (I : Ideal R) {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (evalₐ I n x) = evalₐ I m x := sorry

end AdicCompletion
