/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Admissible.Orthogonal
import StacksCheckRecall.CommandCrossRef

@[expose] public section

/- Lemma 13.40.7 (Stacks 0CQS): right adjointability of a triangulated
subcategory is controlled by its semiorthogonal decomposition with the right
orthogonal; the double-orthogonal and retract consequences are reusable API. -/

@[stacks 0CQS]
#check @CategoryTheory.ObjectProperty.Admissible.Right.domain_eq

@[stacks 0CQS]
#check @CategoryTheory.ObjectProperty.Admissible.Right.isLeftAdjoint_iff

@[stacks 0CQS]
#check @CategoryTheory.ObjectProperty.Admissible.Right.isoClosure_eq

@[stacks 0CQS]
#check @CategoryTheory.ObjectProperty.Admissible.Right.isoClosure_closedUnderRetracts

@[stacks 0CQS]
#check @CategoryTheory.ObjectProperty.Admissible.Right.eq_leftOrthogonal

@[stacks 0CQS]
#check @CategoryTheory.ObjectProperty.Admissible.Right.closedUnderRetracts
