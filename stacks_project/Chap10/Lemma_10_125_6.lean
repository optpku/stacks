/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.KrullDimension.Relative.FiniteType

@[expose] public section

/-!
# Relative-dimension neighborhood recall

The finite-type upper-semicontinuity API belongs to the relative-dimension owner in ReasLib.
The locus-membership form is retained alongside the source-facing equality-at-a-point form because
later arguments usually begin with a bounded-locus hypothesis rather than an equality.

@stack 00QH
-/

/- Lemma 10.125.6, tag 00QH: a point where `relativeDimensionAt R S q = n` has an open
neighborhood contained in `relativeDimensionAtLELocus R S n`. -/
@[stacks 00QH "relative-dimension upper semicontinuity at a point"]
#check @RelativeDimensionAt.exists_openNhdsOf_le_locus

/- Companion API, tag 00QH: every point of `relativeDimensionAtLELocus R S n` has an open
neighborhood contained in the same locus. -/
@[stacks 00QH "bounded relative-dimension locus has local neighborhoods"]
#check @RelativeDimensionAtLELocus.exists_openNhdsOf_mem
