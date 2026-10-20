/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison
public import Mathlib.Tactic.CrossRefAttribute

import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/-!
[stacks 00ZQ]

Lemma 7.50.3 is the standard sheaf-theoretic characterization of the order on Grothendieck
topologies.
-/

@[stacks 00ZQ] #check CategoryTheory.GrothendieckTopology.le_iff_isSheafFor_type
