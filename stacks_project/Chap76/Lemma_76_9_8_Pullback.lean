/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap76.Definition_76_9_1_Arrow
public import stacks_project.Chap76.Definition_76_9_1_FiniteOrder
public import stacks_project.Chap76.Lemma_76_18_1_Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.BaseChange
import StacksCheckRecall

/-!
# Base change of thickenings of algebraic spaces

The fibre product of a thickening of algebraic spaces along an arbitrary
morphism is again a thickening, and the resulting square is a morphism of
thickenings. First-order and finite-order thickenings are likewise stable
under this base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsThickening.pullbackSnd :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {Y Y' X' : AlgebraicGeometry.AlgebraicSpace S}
    (i : Y ⟶ Y') (f' : X' ⟶ Y')
    [AlgebraicGeometry.AlgebraicSpace.IsThickening i],
    AlgebraicGeometry.AlgebraicSpace.IsThickening (pullback.snd i f'))

/- Lemma 76.9.8: the pullback square of a thickening induces the canonical
morphism from the pullback thickening to the original thickening. -/
@[stacks 09ZX] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.pullbackHom :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {Y Y' X' : AlgebraicGeometry.AlgebraicSpace S} →
      (i : Y ⟶ Y') → (f' : X' ⟶ Y') →
        [AlgebraicGeometry.AlgebraicSpace.IsThickening i] →
          AlgebraicGeometry.AlgebraicSpace.Thickening.of (pullback.snd i f') ⟶
            AlgebraicGeometry.AlgebraicSpace.Thickening.of i)

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.pullbackHom_left :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {Y Y' X' : AlgebraicGeometry.AlgebraicSpace S}
    (i : Y ⟶ Y') (f' : X' ⟶ Y')
    [AlgebraicGeometry.AlgebraicSpace.IsThickening i],
    (AlgebraicGeometry.AlgebraicSpace.Thickening.pullbackHom i f').left =
      pullback.fst i f')

#check (AlgebraicGeometry.AlgebraicSpace.Thickening.pullbackHom_right :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {Y Y' X' : AlgebraicGeometry.AlgebraicSpace S}
    (i : Y ⟶ Y') (f' : X' ⟶ Y')
    [AlgebraicGeometry.AlgebraicSpace.IsThickening i],
    (AlgebraicGeometry.AlgebraicSpace.Thickening.pullbackHom i f').right = f')

#check (AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening.pullbackSnd :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {Y Y' X' : AlgebraicGeometry.AlgebraicSpace S}
    (i : Y ⟶ Y') (f' : X' ⟶ Y')
    [AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening i],
    AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening (pullback.snd i f'))

#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening.pullbackSnd :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {Y Y' X' : AlgebraicGeometry.AlgebraicSpace S}
    (i : Y ⟶ Y') (f' : X' ⟶ Y')
    [AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening i],
    AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening (pullback.snd i f'))
