/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.QuasiFinite
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.125.4

@stack 00QF
-/

/- Lemma 10.125.4: for a finite-type map that is quasi-finite at `q`, the Krull dimension of
`S_q` is at most that of `R_(q.under R)`. -/
@[stacks 00QF "quasi-finite local Krull-dimension comparison"]
#check @Algebra.QuasiFiniteAt.ringKrullDim_localizationAtPrime_le
