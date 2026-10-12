/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.RingTheory.Biquadratic.PlaneModel
import StacksCheckRecall

/- Exercise 111.19.1: For the domain
`ℚ[r, s, t] / (s ^ 2 - (r - 1)(r - 2)(r - 3), t ^ 2 - (r + 1)(r + 2)(r + 3))`,
the explicit plane model is `ℚ[X][Y] / (Y ^ 4 - 4X(X ^ 2 + 11)Y ^ 2 + 144(X ^ 2 + 1) ^ 2)`;
the iterated-polynomial presentation is `AdjoinRoot planePoly`. -/
@[stacks 02DT] #check
  (BiquadraticAffine.fractionFieldEquiv :
    FractionRing BiquadraticAffine.PlaneRing ≃ₐ[ℚ] FractionRing BiquadraticAffine.SourceRing)

#check (BiquadraticAffine.instIsDomainSourceRing : IsDomain BiquadraticAffine.SourceRing)
#check (BiquadraticAffine.instIsDomainPlaneRing : IsDomain BiquadraticAffine.PlaneRing)
