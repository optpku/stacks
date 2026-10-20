/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.EffectiveCartier.AffineComplement
import StacksCheckRecall

/-!
# Complements of dense affine opens as effective Cartier divisors

On a regular Noetherian absolutely separated algebraic space, the complement
of a dense affine open subspace is an effective Cartier divisor.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

/- Lemma 71.8.3: Let `S` be a scheme. Let `X` be a regular Noetherian separated
algebraic space over `S`. Let `U ⊂ X` be a dense affine open. Then there exists
an effective Cartier divisor `D ⊂ X` with `U = X \ D`. -/
@[stacks 0DML] #check
  (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.exists_effectiveCartierDivisor_of_isSeparated :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsRegular X] [IsNoetherian X] [IsAbsolutelySeparated X]
      (U : OpenSubspace X) [IsAffine U.X], Dense U.pointsSet →
      ∃ D : ClosedSubspace X,
        IsEffectiveCartierDivisor D.ι ∧ U.pointsSet = D.pointsSetᶜ)

#check
  (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.isEffectiveCartierDivisor_reducedCompl :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsRegular X] [IsNoetherian X] [IsAbsolutelySeparated X]
      (U : OpenSubspace X) [IsAffine U.X], Dense U.pointsSet →
      IsEffectiveCartierDivisor U.reducedComplement.ι)
