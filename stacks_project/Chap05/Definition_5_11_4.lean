/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Catenary
import StacksCheckRecall

@[expose] public section

/-!
# Definition 5.11.4

The reusable catenary-space API is owned by `ReasLib.Topology.Catenary`.
-/

/- Definition 5.11.4: the canonical catenary-space predicate. -/
@[stacks 02I1]
#check @TopologicalSpace.CatenarySpace
