/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.HilbertFunction.Existence
import StacksCheckRecall

universe u

/- Exercise 111.58.7: there exists a Noetherian local ring `R` such that
`associatedGradedHilbertFn R n = n + 1` for every `n`. -/
@[stacks 0D5M] #check (IsLocalRing.exists_noetherian_associatedGradedHilbertFn_eq_succ :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (_ : IsNoetherianRing R),
      ∀ n : ℕ, IsLocalRing.associatedGradedHilbertFn R n = n + 1)
