/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

universe u v

namespace Algebra.FiniteType

/-- Quotienting a finite-type algebra domain over a field by a nonzero nonunit lowers its
Krull dimension by exactly one. -/
theorem ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] {x : A} (hx : x ≠ 0) (hunit : ¬ IsUnit x) :
    ringKrullDim A = ringKrullDim (A ⧸ Ideal.span {x}) + 1 := sorry

end Algebra.FiniteType
