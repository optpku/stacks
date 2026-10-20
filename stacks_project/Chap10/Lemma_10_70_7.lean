/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Radical
import StacksCheckRecall

/-!
# Lemma 10.70.7 recall

@stack 080U

The radical and zero-locus forms are both stable chart-level API in
`AffineBlowupChart`.
-/

@[expose] public section

/- Lemma 10.70.7 (080U): equality of the center and a principal radical gives
regularity and the corresponding localization description. -/
@[stacks 080U "radical regularity criterion"]
#check @AffineBlowupChart.isRegular_of_radical_eq

@[stacks 080U "radical localization criterion"]
#check @AffineBlowupChart.isLocalizationAway_of_radical_eq

@[stacks 080U "zero-locus regularity criterion"]
#check @AffineBlowupChart.isRegular_of_zeroLocus_eq

@[stacks 080U "zero-locus localization criterion"]
#check @AffineBlowupChart.isLocalizationAway_of_zeroLocus_eq
