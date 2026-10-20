/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Divisor.MeromorphicSection.Quotient
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 31.27.3: for two nonzero meromorphic sections of an invertible module on a locally
Noetherian integral scheme, the Weil divisor of the numerator is the Weil divisor of the
denominator plus the principal divisor of their quotient. -/
@[stacks 02SH] #check
  (AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisor_eq_add_principal :
    ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
      (L : X.Modules) [Scheme.Modules.Invertible L]
      (s t : X.toLocallyRingedSpace.meromorphicSections L)
      (hs : s ≠ 0) (ht : t ≠ 0),
      AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisor X L s hs =
        AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisor X L t ht +
          AlgebraicGeometry.Scheme.principalWeilDivisor X
            (AlgebraicGeometry.Scheme.meromorphicSectionQuotient X L s t hs ht))
