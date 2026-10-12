/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.20.5: existence in the valuative criterion is universal specialization lifting. -/
@[stacks 01KE] #check ValuativeCriterion.Existence.eq
