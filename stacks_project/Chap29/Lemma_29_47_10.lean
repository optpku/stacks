/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Seminormalization

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 29.47.10: a scheme is absolutely weakly normal exactly when its canonical absolute weak
normalization morphism is an isomorphism, equivalently when every universal homeomorphism to it
from a reduced scheme is an isomorphism. -/
@[stacks 0H3H] #check
  (AlgebraicGeometry.Scheme.absolutelyWeaklyNormal_iff_isIso_absoluteWeakNormalizationMap :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      AlgebraicGeometry.Scheme.AbsolutelyWeaklyNormal X ↔
        CategoryTheory.IsIso
          ((⊥_ (AlgebraicGeometry.Scheme.AbsoluteWeakNormalizationOver X)).1.hom))

#check
  (AlgebraicGeometry.Scheme.absolutelyWeaklyNormal_iff_universalHomeomorphism_isIso_of_isReduced :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      AlgebraicGeometry.Scheme.AbsolutelyWeaklyNormal X ↔
        ∀ {Y : AlgebraicGeometry.Scheme.{u}} (π : Y ⟶ X),
          AlgebraicGeometry.UniversalHomeomorphism π →
          AlgebraicGeometry.IsReduced Y → CategoryTheory.IsIso π)
