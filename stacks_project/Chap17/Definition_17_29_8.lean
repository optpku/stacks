/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.DifferentialOperator
import StacksCheckRecall

@[expose] public section

/- Definition 17.29.8 (0G3X): relative differential operators on a morphism of ringed spaces. -/
@[stacks 0G3X]
#check @AlgebraicGeometry.RingedSpace.Hom.DifferentialOperator

#check @AlgebraicGeometry.RingedSpace.Hom.differentialOperators
#check @AlgebraicGeometry.RingedSpace.Hom.differentialOperatorGroups
#check @AlgebraicGeometry.RingedSpace.Hom.sourceDifferentialOperators
#check @AlgebraicGeometry.RingedSpace.Hom.sourceDifferentialOperatorGroups
#check @AlgebraicGeometry.RingedSpace.Hom.differentialOperatorBifunctor
#check @AlgebraicGeometry.RingedSpace.Hom.differentialOperatorGroupBifunctor
