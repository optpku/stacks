/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.HilbertFunction

@[expose] public section

universe u

namespace IsLocalRing

/-- There exists a commutative Noetherian local ring whose residue-field
Hilbert function takes the value `n + 1` in every degree `n`. -/
theorem exists_noetherian_associatedGradedHilbertFn_eq_succ :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (_ : IsNoetherianRing R),
      ∀ n : ℕ, associatedGradedHilbertFn R n = n + 1 :=
  sorry

end IsLocalRing
