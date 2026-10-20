module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduction.UniversalHomeomorphism
import StacksCheckRecall

/-!
# The reduction inclusion as a universal homeomorphism of algebraic spaces

The canonical closed immersion from the reduction of an algebraic space is a
universal homeomorphism.
-/

universe u

/- Lemma 67.53.6: The canonical closed immersion from the reduction of an algebraic
space is a universal homeomorphism. -/
@[stacks 08AK] #check
  (AlgebraicGeometry.AlgebraicSpace.instUniversalHomeomorphism_reductionι :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S},
      AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism
        (AlgebraicGeometry.AlgebraicSpace.reductionι X))
