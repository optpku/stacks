/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Constructible.Subspace
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.11: constructible subsets restrict to constructible subspaces
of prespectral spaces. -/
@[stacks 09YI]
#check Topology.IsConstructible.preimage_subtypeVal_of_isConstructible
