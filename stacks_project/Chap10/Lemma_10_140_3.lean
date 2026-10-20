/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.AtPrime.Regularity
import StacksCheckRecall

/-!
# Lemma 10.140.3

@stack 00TT

The three equivalent source clauses are recalled through the two intrinsic point-dimension
criteria. The final regular-local assertion is recalled separately at its canonical localization
interface.
-/

@[expose] public section

/- Lemma 10.140.3: smoothness is equivalent to the upper Kähler-fiber dimension bound. -/
@[stacks 00TT]
#check @Algebra.IsSmoothAt.iff_finrank_kaehlerFiber_le_topologicalKrullDimAt

/- Lemma 10.140.3: smoothness is equivalent to equality in the Kähler-fiber dimension bound. -/
@[stacks 00TT]
#check @Algebra.IsSmoothAt.iff_finrank_kaehlerFiber_eq_topologicalKrullDimAt

/- Lemma 10.140.3: at a smooth prime, the prime localization is regular local. -/
@[stacks 00TT]
#check @Algebra.IsSmoothAt.isRegularLocalRing
