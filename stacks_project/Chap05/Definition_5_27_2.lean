/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Defs.Basic
import StacksCheckRecall

@[expose] public section

universe u

section

variable {X : Type u} [TopologicalSpace X] (x : X)

/- Definition 5.27.2: a point `x` of a topological space is an isolated point exactly when its
singleton is open. -/
@[stacks 06RM "isolated points are points with open singleton"]
#check IsOpen ({x} : Set X)

end
