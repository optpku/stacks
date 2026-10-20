/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CompleteIntersection.OverField
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.135.1

@stack 00S9

This chapter entry is a compatibility facade for the reusable complete-
intersection-over-a-field API.
-/

/- Definition 10.135.1: the neutral owners are
`IsGlobalCompleteIntersection` and `IsLocalCompleteIntersection`. -/
@[stacks 00S9 "(1) global complete intersection"]
#check @IsGlobalCompleteIntersection

@[stacks 00S9 "(1) global complete-intersection specification"]
#check @isGlobalCompleteIntersection_iff

@[stacks 00S9 "(1) source quotient presentation"]
#check @IsGlobalCompleteIntersection.quotientPresentation_or_subsingleton

@[stacks 00S9 "(2) local complete intersection"]
#check @IsLocalCompleteIntersection

@[stacks 00S9 "(2) local complete-intersection specification"]
#check @isLocalCompleteIntersection_iff
