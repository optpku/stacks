/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Spectrum
import StacksCheckRecall

/-!
# Lemma 10.70.11 recall

The density criterion is a neutral affine-blowup-chart API. This file keeps
the textbook label while downstream uses `AffineBlowupChart.Spectrum`
directly.

@stack 052T
-/

@[expose] public section

/- Lemma 10.70.11 (052T): if the distinguished parameter avoids every
minimal prime of the base ring, then `Spec(R[I / a]) → Spec(R)` has dense
range. -/
@[stacks 052T] #check @AffineBlowupChart.denseRange_comap_of_not_mem_minimalPrimes
