/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.UniqueFactorizationDomain.Polynomial
import StacksCheckRecall

/-!
# Polynomial stability of the ACCP property

@stack 0BUE
-/

@[expose] public section

open scoped Polynomial

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/- Lemma 10.120.9 (Stacks `0BUE`): the polynomial ACCP transport is owned by the reusable
`Ideal.polynomial_accp_of_accp` bridge. -/
@[stacks 0BUE]
#check (Ideal.polynomial_accp_of_accp (R := R) :
  {I : Ideal R | I.IsPrincipal}.WellFoundedOn (· > ·) →
    {I : Ideal R[X] | I.IsPrincipal}.WellFoundedOn (· > ·))
