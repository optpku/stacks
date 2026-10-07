module

import ReasLib.CategoryTheory.Pretriangulated.Admissible.Orthogonal
import StacksCheckRecall.CommandCrossRef

@[expose] public section

/- Lemma 13.40.8 (Stacks 0CQT): left adjointability of a triangulated
subcategory is controlled by its semiorthogonal decomposition with the left
orthogonal; the double-orthogonal and retract consequences are reusable API. -/

@[stacks 0CQT]
#check @CategoryTheory.ObjectProperty.Admissible.Left.domain_eq

@[stacks 0CQT]
#check @CategoryTheory.ObjectProperty.Admissible.Left.isRightAdjoint_iff

@[stacks 0CQT]
#check @CategoryTheory.ObjectProperty.Admissible.Left.isoClosure_eq

@[stacks 0CQT]
#check @CategoryTheory.ObjectProperty.Admissible.Left.isoClosure_closedUnderRetracts

@[stacks 0CQT]
#check @CategoryTheory.ObjectProperty.Admissible.Left.eq_rightOrthogonal

@[stacks 0CQT]
#check @CategoryTheory.ObjectProperty.Admissible.Left.closedUnderRetracts
