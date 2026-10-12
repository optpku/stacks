/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import ReasLib.RingTheory.Completion.FaithfullyFlat
public import ReasLib.RingTheory.Flat.Fiber.CohenMacaulay
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohen-Macaulayness and Maximal-Ideal Completion

@stack 07NX
-/

@[expose] public section

open IsLocalRing

universe u

namespace AdicCompletion

/-- Lemma 15.43.3 (07NX): a Noetherian local ring is Cohen-Macaulay exactly when its
maximal-ideal adic completion is Cohen-Macaulay. -/
@[stacks 07NX "Cohen-Macaulayness and maximal-ideal completion"]
theorem cohenMacaulay_iff
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    Module.CohenMacaulay A A ↔
      Module.CohenMacaulay (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal A) A) := sorry

end AdicCompletion
