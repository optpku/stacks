/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Approximation.NoEmbeddedPoints
import StacksCheckRecall

open AlgebraicGeometry
open Set TopologicalSpace

universe u

/- Lemma 31.15.9: A closed subscheme of a Noetherian scheme with no embedded points and
codimension-one irreducible components is an effective Cartier divisor if the ambient stalks
along its support are unique factorization monoids or the ambient scheme is regular. -/
@[stacks 0BXH] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.NoEmbeddedPoints.isEffectiveCartierDivisor_of_stalks_uniqueFactorizationMonoid_or_regular :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (Z : X.IdealSheafData),
      Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme) →
        (∀ ξ : Z.subscheme, ξ ∈ genericPoints Z.subscheme →
          ringKrullDim (X.presheaf.stalk (Z.subschemeι.base ξ)) = 1) →
          ((∀ x : X, x ∈ Z.support →
              UniqueFactorizationMonoid (X.presheaf.stalk x)) ∨
            AlgebraicGeometry.Scheme.Regular X) →
            AlgebraicGeometry.IsEffectiveCartierDivisor Z.subschemeι)
