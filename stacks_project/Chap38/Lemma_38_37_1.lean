/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 38.37.1: an almost blowup square remains an almost blowup square after
base change along any `f : Y ⟶ X`; here `pullback.fst f b` represents
`Y ×_X X' ⟶ Y`, and `I.comap f` represents the center `Y ×_X Z`. -/
@[stacks 0EV7] #check
  (AlgebraicGeometry.IsAlmostBlowupSquare.baseChange :
    ∀ {X X' : AlgebraicGeometry.Scheme.{u}} {b : X' ⟶ X}
      {I : X.IdealSheafData}, AlgebraicGeometry.IsAlmostBlowupSquare b I →
        ∀ {Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X),
          AlgebraicGeometry.IsAlmostBlowupSquare (pullback.fst f b) (I.comap f))
