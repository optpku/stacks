/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.IndSmooth.StandardSmooth

@[expose] public section

/- Lemma 16.3.5: every filtered colimit of smooth ring maps is a filtered
colimit of standard-smooth ring maps. -/
@[stacks 07CI]
#check @RingHom.IndSmooth.indStandardSmooth

#check @RingHom.IndStandardSmooth
