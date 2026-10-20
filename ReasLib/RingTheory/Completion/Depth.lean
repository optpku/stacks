/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReasLib.RingTheory.Completion.FaithfullyFlat
public import ReasLib.RingTheory.Flat.Fiber.Depth
import Mathlib.Tactic.CrossRefAttribute

/-!
# Depth of a Maximal-Ideal Completion

@stack 07NW
-/

@[expose] public section

open IsLocalRing

universe u

namespace AdicCompletion

/-- Lemma 15.43.2 (07NW): a Noetherian local ring and its maximal-ideal adic completion have the
same depth. -/
@[stacks 07NW "depth and maximal-ideal completion"]
theorem moduleDepth_eq (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    moduleDepth A A =
      moduleDepth (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal A) A) := sorry

end AdicCompletion
