/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Definition 26.20.3 (1): the existence part of the valuative criterion. -/
@[stacks 01KD] #check ValuativeCriterion.Existence

/- Definition 26.20.3 (2): the uniqueness part of the valuative criterion. -/
@[stacks 01KD] #check ValuativeCriterion.Uniqueness

#check ValuativeCriterion
#check ValuativeCriterion.iff
