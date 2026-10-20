/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.22.2 (Valuative criterion separatedness): a quasi-separated
morphism satisfying uniqueness in the valuative criterion is separated. -/
@[stacks 01L0] #check IsSeparated.of_valuativeCriterion
