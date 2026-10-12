/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.GlobalSections
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

/- Lemma 28.7.9: if `X` is an integral normal scheme, then its ring of global sections
`Γ(X, ⊤)` is a normal domain. -/
@[stacks 0358] #check
  (AlgebraicGeometry.Scheme.isNormalRing_globalSections :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X],
      X.isNormal → _root_.IsNormalRing (Γ(X, ⊤)))
