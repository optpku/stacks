/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.BaseChange
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.62.6: A flat base change of a local complete intersection morphism is a local
complete intersection morphism. -/
@[stacks 069I] #check
  (AlgebraicGeometry.LocallyOfType.isLocalCompleteIntersection_pullback_snd :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
      [AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f]
      [AlgebraicGeometry.Flat g],
      AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection
        (CategoryTheory.Limits.pullback.snd f g))
