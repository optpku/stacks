/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.TopologicalInvariance

open AlgebraicGeometry CategoryTheory

universe u

/- Theorem 59.45.2: if `f : X ⟶ Y` is integral, universally injective, and
surjective (i.e. a universal homeomorphism, Morphisms Lemma 29.45.5 / 04DF),
the functor `V ↦ X ×_Y V` is an equivalence between schemes étale over `Y`
and schemes étale over `X`. -/
@[stacks 04DZ] #check
  (AlgebraicGeometry.Scheme.smallEtalePullback_isEquivalence_of_universalHomeomorphism :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f],
      (AlgebraicGeometry.Scheme.smallEtalePullback f).IsEquivalence)
