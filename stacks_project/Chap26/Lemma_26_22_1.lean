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

/- Lemma 26.22.1: a separated morphism satisfies the uniqueness part of
the valuative criterion. -/
@[stacks 01KZ] #check IsSeparated.valuativeCriterion
