/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.Topology.Opens.Point

import StacksCheckRecall

@[expose] public section

/-! [stacks 00YE]
Example 7.33.5 is the canonical opens-site point calculation. -/
@[stacks 00YE] #check @Opens.pointFiber_isEmpty_of_not_mem
#check @Opens.pointGrothendieckTopology
#check @TopCat.Presheaf.stalk
#check @TopCat.Presheaf.stalkFunctor
