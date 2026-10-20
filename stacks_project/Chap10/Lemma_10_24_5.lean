/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Local
import StacksCheckRecall

/-!
# Local recovery for principal-open module gluing

The reusable gluing datum is indexed by an arbitrary type.  Finiteness enters
only in local recovery, while overlap compatibility needs no finite-index
hypothesis.

@stack 00EQ
-/

@[expose] public section

@[stacks 00EQ "(1), local recovery of a glued module"]
#check @LocalizedModule.Away.Gluing.localizedProjection_bijective

#check @LocalizedModule.Away.Gluing.localizedProjectionEquiv

@[stacks 00EQ "(2), compatibility on pairwise overlaps"]
#check @LocalizedModule.Away.Gluing.overlapIso_projection_mk
