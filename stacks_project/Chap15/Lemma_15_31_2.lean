/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Presentation.Regularity

/-!
# Lemma 15.31.2

@stack 0BIQ
-/

@[expose] public section

/- Lemma 15.31.2, tag `0BIQ`: the canonical polynomial-quotient presentation map
of the affine blowup chart is bijective for an H1-regular family. -/
@[stacks 0BIQ "Lemma 15.31.2"]
#check @AffineBlowupChart.Presentation.Tuple.map_bijective_of_isH1RegularSequence

#check @AffineBlowupChart.Presentation.Tuple.Quotient
#check @AffineBlowupChart.Presentation.Tuple.map
