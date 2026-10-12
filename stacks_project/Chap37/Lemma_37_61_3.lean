/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.61.3: A flat base change of a perfect morphism is perfect. -/
@[stacks 0688] #check
  (AlgebraicGeometry.LocallyOfType.isPerfectRingMap_pullback_snd :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
      [AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap f]
      [AlgebraicGeometry.Flat g],
      AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap (pullback.snd f g))
