/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Defs.Filter
import StacksCheckRecall

@[expose] public section

/- Definition 5.13.1: a topological space is locally quasi-compact when every point has a
fundamental system of quasi-compact neighbourhoods. Mathlib's separation-free canonical owner is
`LocallyCompactSpace`; its defining field says exactly that every neighbourhood contains a compact
neighbourhood. -/
@[stacks 0068 "locally quasi-compact topological spaces"]
#check LocallyCompactSpace
