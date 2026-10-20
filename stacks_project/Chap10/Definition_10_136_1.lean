/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.Syntomic.Basic
import StacksCheckRecall

/-!
# Definition 10.136.1

@stack 00SL
-/

@[expose] public section

/- Definition 10.136.1, tag `00SL`: a ring map is syntomic when it is flat,
finitely presented, and all of its residue-field fibers are local complete
intersections. -/
@[stacks 00SL]
#check @RingHom.Syntomic

@[stacks 00SL "local complete-intersection fibers"]
#check @RingHom.HasLocalCompleteIntersectionFibers
