/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Flatness.MittagLeffler.RestrictScalars

@[expose] public section

/-!
Chapter 10, Lemma 10.88.12 is the quotient specialization of the reusable restriction-of-scalars
criterion for Mittag-Leffler modules.

@stack 05CR
-/

@[stacks 05CR]
#check @Module.MittagLeffler.RestrictScalars.iff_quotient

@[stacks 05CR "finite-presentation restriction criterion"]
#check @Module.MittagLeffler.RestrictScalars.Surjective.iff_of_finitePresentation

@[stacks 05CR "surjective restriction criterion"]
#check @Module.MittagLeffler.RestrictScalars.iff_of_surjective
