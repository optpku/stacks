/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.FractionRing
public import ReasLib.RingTheory.Etale.Weakly
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integral closure after weakly etale base change

A weakly etale algebra over a normal domain remains integrally closed inside the tensor product
with a fraction field of the base.

@stack 092W
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra.WeaklyEtale

variable {A B K : Type u} [CommRing A] [CommRing B] [Field K]
variable [Algebra A B] [Algebra A K] [IsFractionRing A K] [IsIntegrallyClosed A]

/-- Lemma 15.105.22, Stacks `092W`: if `A` is a normal domain with fraction field `K` and
`A -> B` is weakly etale, then `B` is integrally closed in `B tensor[A] K`. -/
@[stacks 092W "weakly etale base change inside a fraction-field tensor product"]
theorem isIntegrallyClosedIn_tensorProduct_fractionField
    (h : Algebra.WeaklyEtale A B) : IsIntegrallyClosedIn B (B ⊗[A] K) := sorry

end Algebra.WeaklyEtale
