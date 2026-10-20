/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.IntegralClosure.StableSubmodule
import StacksCheckRecall

@[expose] public section

/-!
# Integrality from a stable finite submodule

@stack 052I

The reusable finite stable-submodule criterion is owned by
`Submodule.isIntegral_of_fg_stable`; this file records both it and the literal existential source
form without retaining the chapter-local Cayley--Hamilton calculation.
-/

/- Lemma 10.36.2: a finite stable submodule containing `1` forces integrality. -/
@[stacks 052I "finite stable-submodule criterion"]
#check @Submodule.isIntegral_of_fg_stable

@[stacks 052I "source existential form"]
#check @Submodule.isIntegral_of_exists_fg_stable
