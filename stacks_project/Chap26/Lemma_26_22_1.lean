/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.22.1: a separated morphism satisfies the uniqueness part of
the valuative criterion. -/
@[stacks 01KZ] #check IsSeparated.valuativeCriterion
