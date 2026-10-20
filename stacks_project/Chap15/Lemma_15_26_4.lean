/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.StrictTransform
import StacksCheckRecall

/-!
# Lemma 15.26.4

@stack 0CZN

The chartwise finite-locally-free criterion for strict transforms is owned by the reusable affine
blowup-chart API.
-/

@[expose] public section

/- Lemma 15.26.4: local freeness of rank `k` away from the `k`th Fitting locus makes every
corresponding affine-chart strict transform finite locally free of rank `k`. -/
@[stacks 0CZN "Lemma 15.26.4"]
#check @AffineBlowupChart.StrictTransform.finiteLocallyFreeOfRank
