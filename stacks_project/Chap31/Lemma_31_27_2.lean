/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Divisor.MeromorphicSection

universe u

/- Lemma 31.27.2 (1): the supports of prime divisors at whose generic points a nonzero
meromorphic section does not come from the invertible module stalk form a locally finite family. -/
@[stacks 02SG] #check
  (@AlgebraicGeometry.Scheme.locallyFinite_primeDivisors_nonzeroMeromorphicSection_not_regularAt :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsIntegral X]
      (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (s : X.toLocallyRingedSpace.meromorphicSections L) (_ : s ≠ 0),
      LocallyFinite fun Z : AlgebraicGeometry.PrimeDivisor X ↦
        {x | ¬ AlgebraicGeometry.LocallyRingedSpace.MeromorphicSection.IsRegularAt
            s Z.genericPoint ∧ x ∈ (Z.support : Set X)})

/- Lemma 31.27.2 (2): the supports of prime divisors on which a nonzero meromorphic section has
nonzero intrinsic order form a locally finite family. -/
@[stacks 02SG] #check
  (@AlgebraicGeometry.Scheme.locallyFinite_nonzeroMeromorphicSectionWeilDivisorCoeff_ne_zero :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsIntegral X]
      (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0),
      LocallyFinite fun Z : AlgebraicGeometry.PrimeDivisor X ↦
        if AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisorCoeff L s hs Z = 0 then
          (∅ : Set X)
        else
          (Z.support : Set X))
