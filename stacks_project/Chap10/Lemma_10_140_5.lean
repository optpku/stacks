/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.AtPrime.Regularity
import StacksCheckRecall

/-!
# Lemma 10.140.5

@stack 00TV
-/

@[expose] public section

/- Lemma 10.140.5 [stacks 00TV]: canonical recall that smoothness at a prime with separable
residue field is equivalent to regularity of its prime localization. -/
@[stacks 00TV]
#check @Algebra.IsSmoothAt.iff_isRegularLocalRing_of_separableResidueField
