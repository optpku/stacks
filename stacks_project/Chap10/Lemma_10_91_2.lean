/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler.SupportingSubmodule
import StacksCheckRecall

/-!
@stack 059S
-/

@[expose] public section

/- Chap10 Lemma 10 91 2: a flat module is Mittag-Leffler exactly when every tensor over a finite
free module has a least supporting submodule. -/
@[stacks 059S]
#check @Module.MittagLeffler.iff_exists_least_tensorSupport

@[stacks 059S "tensor-support predicate"]
#check @Submodule.SupportsTensor

@[stacks 059S "least tensor support existence"]
#check @Module.MittagLeffler.exists_least_tensorSupport

@[stacks 059S "Mittag-Leffler from least tensor support"]
#check @Module.MittagLeffler.of_exists_least_tensorSupport
