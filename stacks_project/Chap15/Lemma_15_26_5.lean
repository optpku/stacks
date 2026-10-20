/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.StrictTransform
import StacksCheckRecall

/-!
# Lemma 15.26.5

@stack 0BBJ

The existence of a finitely generated flattening center is owned by the reusable strict-transform
API.
-/

@[expose] public section

/- Lemma 15.26.5: finite local freeness after inverting `f` yields a finitely generated center
with the same vanishing locus whose affine-chart strict transforms are finite locally free of the
same rank. -/
@[stacks 0BBJ "Lemma 15.26.5"]
#check @AffineBlowupChart.StrictTransform.existsCenterFiniteLocallyFreeOfRank
