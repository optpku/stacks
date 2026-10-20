/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Rank.Invertible
import StacksCheckRecall

@[expose] public section

/- Lemma 17.25.4, forward direction: a finite locally free module sheaf of rank one is invertible.
The ringed-site owner is more general than the source's ringed-space specialization. -/
@[stacks 0B8M "forward"]
#check @SheafOfModules.RingedSite.rankOne_isInvertible

/- Lemma 17.25.4, converse direction: if every stalk ring is local, then every invertible module
sheaf is finite locally free of rank one. -/
@[stacks 0B8M "converse"]
#check @AlgebraicGeometry.RingedSpace.rankOne_of_isInvertible

#check @AlgebraicGeometry.RingedSpace.rankOne_iff_isInvertible
