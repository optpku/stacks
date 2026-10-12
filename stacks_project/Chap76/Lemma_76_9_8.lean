/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_9_8_Pullback
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 76.9.8 (1): the pullback of a thickening `i : Y ⟶ Y'` along
`f' : X' ⟶ Y'` gives a morphism of thickenings from
`pullback.snd i f' : Y ×[Y'] X' ⟶ X'` to `i`. -/
@[stacks 09ZX] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.pullbackHom :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {Y Y' X' : AlgebraicGeometry.AlgebraicSpace S} →
      (i : Y ⟶ Y') → (f' : X' ⟶ Y') →
        [AlgebraicGeometry.AlgebraicSpace.IsThickening i] →
          AlgebraicGeometry.AlgebraicSpace.Thickening.of (pullback.snd i f') ⟶
            AlgebraicGeometry.AlgebraicSpace.Thickening.of i)

/- Lemma 76.9.8 (2): the pullback of a first-order thickening is a first-order
thickening. -/
@[stacks 09ZX] #check (AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening.pullbackSnd :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {Y Y' X' : AlgebraicGeometry.AlgebraicSpace S}
    (i : Y ⟶ Y') (f' : X' ⟶ Y')
    [AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening i],
    AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening (pullback.snd i f'))

/- Lemma 76.9.8 (3): the pullback of a finite-order thickening is a finite-order
thickening. -/
@[stacks 09ZX] #check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.pullbackSnd :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {Y Y' X' : AlgebraicGeometry.AlgebraicSpace S}
    (i : Y ⟶ Y') (f' : X' ⟶ Y')
    [AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening i],
    AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening (pullback.snd i f'))
