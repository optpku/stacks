/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Cohomology
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.GradedSections
open scoped AlgebraicGeometry

universe u

/- Lemma 30.17.3: for a quasi-compact and quasi-separated scheme, localizing the graded
cohomology of all integral twists at a degree-one section gives the cohomology on its
nonvanishing open; the comparison sends `ξ / s^n` to the restriction of `ξ` contracted by
`s^{-n}`. -/
@[stacks 09MR] #check
  (AlgebraicGeometry.Scheme.Modules.GradedSections.localizedTwistedCohomologyComparison_bijective :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (F : X.Modules) [F.IsQuasicoherent] (s : Γ(L, ⊤)) (p : ℕ),
      Function.Bijective (localizedTwistedCohomologyComparison L F s p))

#check
  (AlgebraicGeometry.Scheme.Modules.GradedSections.localizedTwistedCohomologyComparison_apply_mk :
    ∀ {X : Scheme.{u}} (L : X.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (F : X.Modules) (s : Γ(L, ⊤)) (p n : ℕ)
      (ξ : twistedCohomologyDegree L F p (n : ℤ)),
      localizedTwistedCohomologyComparison L F s p
          (localizedTwistedCohomologyMk L F s p n ξ) =
        localizedTwistedCohomologyFractionValue L F s p n ξ)
