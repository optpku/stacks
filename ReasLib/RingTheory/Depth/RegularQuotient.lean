/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Depth
public import Mathlib.Algebra.Regular.Defs

@[expose] public section

open scoped ENat

universe u

/-- Quotienting a Noetherian local ring by a regular element of its maximal ideal
lowers every natural depth threshold by one. -/
theorem moduleDepth_quotient_span_singleton_ge_iff
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) (n : ℕ) :
    ((n : ℕ∞) ≤ moduleDepth A (A ⧸ Ideal.span {f})) ↔
      (((n + 1 : ℕ) : ℕ∞) ≤ moduleDepth A A) := sorry
