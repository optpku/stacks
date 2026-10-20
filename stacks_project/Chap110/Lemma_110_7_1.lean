/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Noncomplete
import StacksCheckRecall

@[expose] public section

universe u

open IsLocalRing

/- Lemma 110.7.1: there exists a local ring `R` and a maximal ideal `m` such that the
`m`-adic completion `AdicCompletion m R` is local, its maximal ideal is not
`m.map (algebraMap R (AdicCompletion m R))`, it is not a complete local ring, and it is
not `m`-adically complete as an `R`-module. -/
@[stacks 05JC]
#check (AdicCompletion.Counterexample.exists_local_not_completeLocalRing :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (m : Ideal R)
      (_ : m.IsMaximal) (_ : IsLocalRing (AdicCompletion m R)),
      maximalIdeal (AdicCompletion m R) ≠
          m.map (algebraMap R (AdicCompletion m R)) ∧
        ¬ IsCompleteLocalRing (AdicCompletion m R) ∧
        ¬ IsAdicComplete m (AdicCompletion m R))
