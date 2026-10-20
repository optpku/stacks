/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen.Basis

@[expose] public section

open scoped AlgebraicGeometry

universe u

/- Lemma 28.26.6: if the positive tensor-power nonvanishing opens of an invertible module
form a basis, then the affine members of the same family form a basis. -/
@[stacks 01PX] #check
  (AlgebraicGeometry.Scheme.Modules.isBasis_affine_positiveTensorPowerNonvanishingOpens :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L],
      TopologicalSpace.Opens.IsBasis
          (AlgebraicGeometry.Scheme.Modules.positiveTensorPowerNonvanishingOpens L) →
        TopologicalSpace.Opens.IsBasis
          {U : X.Opens |
            U ∈ AlgebraicGeometry.Scheme.Modules.positiveTensorPowerNonvanishingOpens L ∧
              AlgebraicGeometry.IsAffineOpen U})
