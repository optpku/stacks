/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.IdempotentLifting.Correction
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Ring.Defs

@[expose] public section

-- Theorem-local support for Lemma 10.77.5.

open Polynomial

universe u

section

variable {A : Type u} [Ring A]

/-- Helper for Lemma 10.77.5: in a possibly noncommutative ring, a nilpotent idempotency defect
can be corrected by a right-multiple of that defect.  The correction element is obtained from the
shared polynomial correction API, evaluated at `e`, so it is in fact a polynomial in `e`. -/
theorem exists_idempotent_eq_add_defect_mul_aeval (e : A)
    (hx : IsNilpotent (e ^ 2 - e)) :
    ∃ c : A, IsIdempotentElem (e + (e ^ 2 - e) * c) := sorry

end
