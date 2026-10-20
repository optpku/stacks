/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Action.JointlySurjective
public import StacksCheckRecall.CommandCrossRef

/-!
# Example 7.6.5

The site of universe-sized `G`-sets is the reusable
`Action.jointlySurjectiveTopology`; its primitive precoverage and covering-sieve characterization
are owned by the shared leaf rather than by this chapter-facing recall module.
-/

@[expose] public section

@[stacks 00VK "(1)"] #check Action.jointlySurjectivePrecoverage
@[stacks 00VK "(2)"] #check Action.jointlySurjectiveTopology
@[stacks 00VK "(3)"] #check Action.mem_jointlySurjectiveTopology_iff
