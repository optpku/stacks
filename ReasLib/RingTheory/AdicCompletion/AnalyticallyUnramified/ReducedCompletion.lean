/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.Counterexample
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.Nagata
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.Reduced
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reduced local rings and their completions

This leaf records the reducedness consequences and counterexample for maximal-ideal adic
completion.

@stack 07NZ
-/

@[expose] public section

open IsLocalRing

universe u

namespace IsAnalyticallyUnramified

/-- A Noetherian local ring is reduced when its maximal-ideal adic completion is
reduced. -/
@[stacks 07NZ "(1), reducedness descends from completion"]
theorem isReduced_of_completion {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsReduced (AdicCompletion (maximalIdeal A) A)] :
    IsReduced A := sorry

/-- A reduced Noetherian local ring can have a nonreduced maximal-ideal adic
completion. -/
@[stacks 07NZ "(2), reduced ring with nonreduced completion"]
theorem exists_reduced_with_nonreduced_completion :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A) (_ : IsLocalRing A),
      IsReduced A ∧ ¬ IsReduced (AdicCompletion (maximalIdeal A) A) := sorry

end IsAnalyticallyUnramified

namespace NagataRing

/-- A local Nagata ring is reduced if and only if its maximal-ideal adic
completion is reduced. -/
@[stacks 07NZ "(3), reducedness criterion for Nagata rings"]
theorem isReduced_iff_completion_isReduced {A : Type u} [CommRing A] [IsLocalRing A]
    [NagataRing A] :
    IsReduced A ↔ IsReduced (AdicCompletion (maximalIdeal A) A) := sorry

end NagataRing
