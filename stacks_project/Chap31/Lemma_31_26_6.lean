module

import ReasLib.AlgebraicGeometry.Scheme.Divisor.Principal
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 31.26.6: For a locally Noetherian integral scheme `X` and
`f g : X.functionFieldˣ`, the principal Weil divisor of `f * g` is the sum of
the principal Weil divisors of `f` and `g`. -/
@[stacks 02RP] #check
  (AlgebraicGeometry.Scheme.principalWeilDivisor_mul :
    ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (f g : X.functionFieldˣ),
      AlgebraicGeometry.Scheme.principalWeilDivisor X (f * g) =
        AlgebraicGeometry.Scheme.principalWeilDivisor X f +
          AlgebraicGeometry.Scheme.principalWeilDivisor X g)
