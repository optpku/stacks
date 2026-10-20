/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DualNumber.Basis
import StacksCheckRecall

@[expose] public section

universe u

open scoped DualNumber

variable (R : Type u) [CommRing R]

/- Definition 111.35.1: for any ring `R`, `DualNumber R` (notation `R[ε]`) is the ring of dual
numbers. As an `R`-module it is free with ordered basis `1`, `ε`, and the ring structure is
determined by `ε ^ 2 = 0`. -/
@[stacks 029D] #check (DualNumber.finTwoProd_eq_one_eps R :
    Module.Basis.finTwoProd R 0 = (1 : R[ε]) ∧
      Module.Basis.finTwoProd R 1 = (ε : R[ε]))

#check DualNumber.eps

#check (DualNumber.eps_pow_two (R := R) : (ε : R[ε]) ^ 2 = 0)

#check (algebraMap R R[ε] : R →+* R[ε])
