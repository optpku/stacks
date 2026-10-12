/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Submersive
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u v

/- Lemma 34.10.14: a `V` covering family induces a universally submersive
morphism from the coproduct of its source schemes to the target. -/
@[stacks 0ETP] #check
  (AlgebraicGeometry.universallySubmersive_sigmaDesc_of_isVCovering :
    ∀ {ι : Type v} {X : AlgebraicGeometry.Scheme.{u}} [Small.{u} ι]
      (Xi : ι → AlgebraicGeometry.Scheme.{u}) (f : ∀ i, Xi i ⟶ X),
        AlgebraicGeometry.IsVCovering X Xi f →
          AlgebraicGeometry.UniversallySubmersive
            (CategoryTheory.Limits.Sigma.desc f))
