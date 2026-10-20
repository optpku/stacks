/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.Baire
import StacksCheckRecall

/-!
# Lemma 15.36.4 (0CQV)

@stack 0CQV
-/

@[expose] public section

/- Lemma 15.36.4 (0CQV): one member of a countable closed-subgroup cover is open. -/
@[stacks 0CQV]
#check @AddSubgroup.exists_isOpen_of_iUnion_eq_univ
