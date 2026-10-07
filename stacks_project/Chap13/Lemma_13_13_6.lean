module

import ReasLib.CategoryTheory.Filtration.Derived.Forget.Triangulated
import ReasLib.CategoryTheory.Filtration.Derived.GradedObject
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.13.6

The associated-graded, graded-piece, and forgetful functors on the finite filtered derived
category are owned by neutral ReasLib leaves.  Their localization certificates remain explicit
inputs to data-bearing lifts, while the chapter entry is only the `05S3` recall surface.
-/

/- Associated graded before and after finite filtered localization. -/
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.homotopy
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.Inverts
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.inverts
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.lift
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.facIso
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.Lift.isTriangulated

/- Direct graded pieces and the graded-object-valued companion view. -/
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.homotopy
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.compIso
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.lift
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.facIso
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.GradedPiece.Lift.isTriangulated
@[stacks 05S3] #check
  CategoryTheory.GradedObject.Derived.Evaluation.functor
@[stacks 05S3] #check
  CategoryTheory.GradedObject.Derived.Evaluation.compEval
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.Graded.functor
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.Graded.evalIso

/- Forgetting a finite filtration, including its acyclicity bridge and localization lift. -/
@[stacks 05S3] #check CategoryTheory.FilteredObject.Finite.Forget.homotopy
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.Finite.Acyclic.forget_of_associatedGraded
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.Forget.homotopy
@[stacks 05S3] #check CategoryTheory.FilteredObject.FiniteDerived.Forget.Inverts
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.Forget.inverts
@[stacks 05S3] #check CategoryTheory.FilteredObject.FiniteDerived.Forget.lift
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.Forget.facIso
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.Forget.Lift.commShift
@[stacks 05S3] #check
  CategoryTheory.FilteredObject.FiniteDerived.Forget.Lift.isTriangulated
