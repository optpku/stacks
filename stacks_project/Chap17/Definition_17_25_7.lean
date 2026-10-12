/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GradedSections
import StacksCheckRecall

@[expose] public section

/- Definition 17.25.7 (01CV): the nonnegative graded ring of global sections of the tensor
powers of an invertible module sheaf. -/
@[stacks 01CV "graded ring"]
#check @AlgebraicGeometry.RingedSpace.GradedSections.ring

/- Definition 17.25.7 (01CV): the integer-graded module of global sections of twists by an
invertible module sheaf. -/
@[stacks 01CV "twisted graded module"]
#check @AlgebraicGeometry.RingedSpace.GradedSections.twisted

#check @AlgebraicGeometry.RingedSpace.GradedSections.instGCommRing
#check @AlgebraicGeometry.RingedSpace.GradedSections.instGmodule
