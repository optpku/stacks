/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Shrinking.RelativeTuplewise
import StacksCheckRecall

@[expose] public section

/-
Lemma 5.13.7 is owned by the relative compact-subset shrinking API. The chapter entry retains
only the canonical predicate, its extensional interface, and the tagged existence theorem.
-/

#check TopologicalSpace.IsRelativeTuplewiseShrinking
#check TopologicalSpace.isRelativeTuplewiseShrinking_iff

/- Lemma 5.13.7: a compact subset whose distinct points have separated ambient neighborhoods
admits a tuple-intersection shrinking. -/
@[stacks 0CY5]
#check IsCompact.exists_relative_tuplewise_shrinking
