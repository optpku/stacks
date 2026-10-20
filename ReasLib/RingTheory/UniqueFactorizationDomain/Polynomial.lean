/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.UniqueFactorizationDomain.ACCP

/-!
# ACCP for polynomial rings

This leaf exposes the canonical polynomial `WfDvdMonoid` instance as a direct transport of the
ascending-chain condition on principal ideals.  The result is stated at the semiring/domain layer;
the chapter's commutative-ring statement is a specialization.
-/

@[expose] public section

open scoped Polynomial

universe u

namespace Ideal

variable {R : Type u} [CommSemiring R] [IsDomain R]

/-- Lemma 10.120.9 (Stacks `0BUE`): ACCP for a domain is inherited by its polynomial ring. -/
@[stacks 0BUE]
theorem polynomial_accp_of_accp
    (hacc : {I : Ideal R | I.IsPrincipal}.WellFoundedOn (· > ·)) :
    {I : Ideal R[X] | I.IsPrincipal}.WellFoundedOn (· > ·) := sorry

end Ideal
