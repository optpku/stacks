/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AmpleCriterion
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 30.17.8: let `X` be a quasi-affine scheme. If
`H^p(X, 𝒪_X) = 0` for every `p > 0`, then `X` is affine. -/
@[stacks 0EBE] #check
  (AlgebraicGeometry.Scheme.IsQuasiAffine.isAffine_of_structureSheaf_higherCohomology_isZero :
    ∀ {X : Scheme.{u}}, X.IsQuasiAffine →
      (∀ p : ℕ, 0 < p →
        IsZero (RingedSpace.moduleCohomology
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) p)) →
      IsAffine X)
