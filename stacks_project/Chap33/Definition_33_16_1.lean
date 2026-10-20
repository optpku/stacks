/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DualNumber.Basis
import StacksCheckRecall

/-!
# Definition 33.16.1

The canonical basis of the dual numbers.

@stack 0B29
-/

@[expose] public section

open scoped DualNumber

universe u

variable (R : Type u) [CommRing R]

/- Definition 33.16.1: The dual numbers over `R` have ordered basis `1`, `ε`. -/
@[stacks 0B29] #check
  (DualNumber.finTwoProd_eq_one_eps R :
    Module.Basis.finTwoProd R 0 = (1 : R[ε]) ∧
      Module.Basis.finTwoProd R 1 = (ε : R[ε]))

#check (algebraMap R R[ε] : R →+* R[ε])

#check (DualNumber.eps_pow_two (R := R) : (ε : R[ε]) ^ 2 = 0)
