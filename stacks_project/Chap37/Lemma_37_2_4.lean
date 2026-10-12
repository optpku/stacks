/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.BaseChange
import StacksCheckRecall

open CategoryTheory Limits

universe u

/- Lemma 37.2.4 (1): the pullback of a thickening `i : S ⟶ S'` along
`f' : X' ⟶ S'` gives a morphism of thickenings from
`pullback.snd i f' : S ×[S'] X' ⟶ X'` to `i`. -/
@[stacks 09ZU] #check (AlgebraicGeometry.Thickening.pullbackHom :
  {S S' X' : AlgebraicGeometry.Scheme.{u}} →
    (i : S ⟶ S') → (f' : X' ⟶ S') → [AlgebraicGeometry.IsThickening i] →
      AlgebraicGeometry.Thickening.of (pullback.snd i f') ⟶
        AlgebraicGeometry.Thickening.of i)

/- Lemma 37.2.4 (2): the pullback of a first-order thickening is a first-order
thickening. -/
@[stacks 09ZU] #check (AlgebraicGeometry.IsFirstOrderThickening.pullbackSnd :
  ∀ {S S' X' : AlgebraicGeometry.Scheme.{u}} (i : S ⟶ S') (f' : X' ⟶ S')
    [AlgebraicGeometry.IsFirstOrderThickening i],
    AlgebraicGeometry.IsFirstOrderThickening (pullback.snd i f'))

/- Lemma 37.2.4 (3): the pullback of a finite-order thickening is a finite-order
thickening. -/
@[stacks 09ZU] #check (AlgebraicGeometry.IsFiniteOrderThickening.pullbackSnd :
  ∀ {S S' X' : AlgebraicGeometry.Scheme.{u}} (i : S ⟶ S') (f' : X' ⟶ S')
    [AlgebraicGeometry.IsFiniteOrderThickening i],
    AlgebraicGeometry.IsFiniteOrderThickening (pullback.snd i f'))
