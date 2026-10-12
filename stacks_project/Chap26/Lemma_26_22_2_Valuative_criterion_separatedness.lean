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

/- Lemma 26.22.2 (Valuative criterion separatedness): a quasi-separated
morphism satisfying uniqueness in the valuative criterion is separated. -/
@[stacks 01L0] #check IsSeparated.of_valuativeCriterion
