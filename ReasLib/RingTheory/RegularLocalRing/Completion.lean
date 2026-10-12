/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import ReasLib.RingTheory.Completion.FaithfullyFlat
public import ReasLib.RingTheory.RegularLocalRing.Fiber
public import ReasLib.RingTheory.RegularLocalRing.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular local rings and completion

This leaf owns invariance of regular-locality under completion at the maximal
ideal of a Noetherian local ring.

@stack 07NY
-/

@[expose] public section

open IsLocalRing

universe u

/-- Lemma 15.43.4 (07NY): a Noetherian local ring is regular if and only if its
maximal-ideal adic completion is regular. -/
@[stacks 07NY "regularity and maximal-ideal completion"]
theorem isRegularLocalRing_iff_isRegularLocalRing_maximalIdeal_adicCompletion
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    IsRegularLocalRing A ↔
      IsRegularLocalRing (AdicCompletion (maximalIdeal A) A) := sorry
