/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.43.5: a locally projective morphism is proper. -/
@[stacks 01WC] #check
  (AlgebraicGeometry.LocallyProjective.isProper :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyProjective f], AlgebraicGeometry.IsProper f)
