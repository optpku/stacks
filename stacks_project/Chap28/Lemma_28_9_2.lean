/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Regular
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.9.2 (1): a scheme `X` is regular if and only if `X` is locally Noetherian and every
local ring `X.presheaf.stalk x` is a regular local ring. -/
@[stacks 02IT] #check
  (AlgebraicGeometry.Scheme.regular_iff_isLocallyNoetherian_and_forall_isRegularLocalRing_stalk :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.Scheme.Regular X ↔
        AlgebraicGeometry.IsLocallyNoetherian X ∧
          ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))

/- Lemma 28.9.2 (2): a scheme `X` is regular if and only if `X` is locally Noetherian and every
closed point `x ∈ X` has regular local ring `X.presheaf.stalk x`. -/
@[stacks 02IT] #check
  (AlgebraicGeometry.Scheme.regular_iff_closedPointStalk :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.Scheme.Regular X ↔
        AlgebraicGeometry.IsLocallyNoetherian X ∧
          ∀ x : X, x ∈ closedPoints X →
            IsRegularLocalRing (X.presheaf.stalk x))
