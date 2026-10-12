/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.TensorInternalHom
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry.RingedSpace

/- Remark 20.42.10 (0FXP): the tensor/internal-Hom comparison on a ringed-space derived
category is the specialization of the generic closed-monoidal owner.  The owner factors through
the already shared tensor/internal-Hom comparison and the source-order currying isomorphism. -/
@[stacks 0FXP]
#check @CategoryTheory.MonoidalClosed.tensorHomComparison

#check @CategoryTheory.MonoidalClosed.tensorHomComparison_spec
#check @CategoryTheory.MonoidalClosed.tensorHomComparison_natural_leftSource
#check @CategoryTheory.MonoidalClosed.tensorHomComparison_natural_leftTarget
#check @CategoryTheory.MonoidalClosed.tensorHomComparison_natural_rightSource
#check @CategoryTheory.MonoidalClosed.tensorHomComparison_natural_rightTarget
#check @CategoryTheory.MonoidalClosed.tensorInternalHomComparison
#check @CategoryTheory.MonoidalClosed.internalHomTensorIso

end AlgebraicGeometry.RingedSpace
