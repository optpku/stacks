/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.39.16

@stack 00HQ
-/

/-!
# Closed points and faithful flatness

Compatibility entry point for the closed-point criteria owned by
`ReasLib.RingTheory.RingHom.FaithfullyFlat`.
-/

/- Lemma 10.39.16: the source's surjectivity and faithful-flatness criteria
are reusable ring-hom APIs, rather than Chap10-local declarations. -/
@[stacks 00HQ "closed-point surjectivity"]
#check @specComap_surjective_iff_closedPoints_subset_range
@[stacks 00HQ "faithful-flat closed-point criterion"]
#check @faithfullyFlat_iff_closedPoints_subset_range
