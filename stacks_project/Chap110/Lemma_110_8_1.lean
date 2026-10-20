/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Counterexample
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 110.8.1: there exists a ring `R` that is `I`-adically complete for a principal
ideal `I`, together with a principal ideal `J`, such that the quotient `R ⧸ J` is not
`I`-adically complete. -/
@[stacks 05JE] #check (IsAdicComplete.exists_principal_quotient_not_adicComplete :
    ∃ (R : Type u) (_ : CommRing R) (I J : Ideal R),
      I.IsPrincipal ∧ IsAdicComplete I R ∧ J.IsPrincipal ∧
        ¬ IsAdicComplete I (R ⧸ J))
