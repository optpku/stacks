/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Constructible.Subspace
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.9: constructible subsets of closed subspaces with retrocompact
complement have constructible ambient image. -/
@[stacks 09YG "constructible subsets of closed subspaces"]
#check Topology.IsConstructible.image_subtypeVal_of_isRetrocompact_compl
