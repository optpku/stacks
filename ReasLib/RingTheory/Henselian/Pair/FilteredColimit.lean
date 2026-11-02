/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import ReasLib.RingTheory.Henselian.Pair.Category
import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered colimits of pair Henselizations

Pair Henselization is a left adjoint and therefore preserves filtered colimits.

@stack 0A04
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace RingPairCat

/-- Lemma 15.12.5: the pair-Henselization functor preserves filtered colimits.
The right-adjoint witness is an explicit parameter so the statement does not select
Henselization data from the deferred existence theorem. -/
@[stacks 0A04 "Lemma 15.12.5"]
instance pairHenselization_preservesFilteredColimits
    [henselianPairInclusion.{u}.IsRightAdjoint] :
    PreservesFilteredColimits henselianPairInclusion.leftAdjoint := sorry

end RingPairCat
