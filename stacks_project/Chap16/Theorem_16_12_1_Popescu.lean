/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndSmooth.Popescu
import StacksCheckRecall

@[expose] public section

/- Theorem 16.12.1 (Popescu): regular Noetherian ring maps are filtered
colimits of smooth maps. -/
@[stacks 07GC]
#check @RingHom.Regular.indSmooth

#check @RingHom.Regular.hasFactorisations
