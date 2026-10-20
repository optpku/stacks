/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Depth.LinearMap
import StacksCheckRecall

/-!
# Lemma 15.23.10

This file recalls the two local depth bounds for modules of linear maps.

@stack 0AV5
-/

@[expose] public section

/- Lemma 15.23.10 (1): depth at least one passes from a finite codomain to the linear-map
module. -/
@[stacks 0AV5 "Lemma 15.23.10 (1)"]
#check @LinearMap.moduleDepth_ge_one_of_codomain

/- Lemma 15.23.10 (2): depth at least two passes from a finite codomain to the linear-map
module. -/
@[stacks 0AV5 "Lemma 15.23.10 (2)"]
#check @LinearMap.moduleDepth_ge_two_of_codomain
