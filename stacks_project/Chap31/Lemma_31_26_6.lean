/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
