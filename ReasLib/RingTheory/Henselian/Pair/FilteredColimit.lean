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

/-- Local instance justification (instance diamond): select the canonical right-adjoint witness
for the inclusion of henselian pairs only in this preservation statement. -/
local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

/-- Lemma 15.12.5: the pair-Henselization functor preserves filtered colimits. -/
@[stacks 0A04 "Lemma 15.12.5"]
instance pairHenselization_preservesFilteredColimits :
    PreservesFilteredColimits henselianPairInclusion.leftAdjoint := sorry

end RingPairCat
