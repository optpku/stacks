/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normalization.Normal

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.54.9: Let `X` be a scheme with locally finitely many irreducible components. The
normalization morphism `X.normalizationTo` is an isomorphism if and only if `X` is normal. -/
@[stacks 0H7D] #check
  (AlgebraicGeometry.Scheme.isIso_normalizationTo_iff_isNormal :
    ∀ (X : Scheme.{u}), [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] →
      IsIso X.normalizationTo ↔ X.isNormal)
