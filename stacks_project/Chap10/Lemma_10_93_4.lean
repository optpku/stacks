/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler.Projective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.93.4

@stack 05A0
-/

/- Chap10 Lemma 10 93 4: a universally injective submodule of a flat Mittag-Leffler module is
projective when it is a direct sum of countably generated submodules. -/
@[stacks 05A0]
#check @LinearMap.UniversallyInjective.projective
