/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.ProjectiveSpace.Relative.TwistCohomology
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 30.8.3

For projective `n`-space over a scheme, the higher direct images of the degree-`d` twisting
sheaf are the degree-`d` polynomial piece in the active degree-zero case, the internal dual of
the complementary piece in the active top-degree case, and zero outside these cases.
-/
@[stacks 01XW] #check
  (AlgebraicGeometry.ProjectiveSpace.relativeTwistingSheaf_higherDirectImage_cases :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (n : ℕ) (d : ℤ),
      (0 ≤ d →
        IsIsomorphic
          (((AlgebraicGeometry.Scheme.Modules.pushforward
            (AlgebraicGeometry.ProjectiveSpace.toBase n S)).rightDerived 0).obj
              (AlgebraicGeometry.ProjectiveSpace.relativeTwistingSheaf S n d))
          (AlgebraicGeometry.ProjectiveSpace.relativeGradedPiece S n d)) ∧
      (d < 0 →
        IsIsomorphic
          (((AlgebraicGeometry.Scheme.Modules.pushforward
            (AlgebraicGeometry.ProjectiveSpace.toBase n S)).rightDerived n).obj
              (AlgebraicGeometry.ProjectiveSpace.relativeTwistingSheaf S n d))
          (AlgebraicGeometry.ProjectiveSpace.relativeTopCohomologyDual S n d)) ∧
      (∀ q : ℕ, ¬ (q = 0 ∧ 0 ≤ d) → ¬ (q = n ∧ d < 0) →
        IsZero
          (((AlgebraicGeometry.Scheme.Modules.pushforward
            (AlgebraicGeometry.ProjectiveSpace.toBase n S)).rightDerived q).obj
              (AlgebraicGeometry.ProjectiveSpace.relativeTwistingSheaf S n d))))
