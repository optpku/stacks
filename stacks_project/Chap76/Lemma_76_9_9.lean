/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Composition
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 76.9.9: If `X ⟶ X'` and `X' ⟶ X''` are thickenings of algebraic spaces
over a scheme `S`, then the composite `X ⟶ X''` is a thickening. -/
@[stacks 0BPH] #check
  (AlgebraicGeometry.AlgebraicSpace.IsThickening.comp :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X X' X'' : AlgebraicGeometry.AlgebraicSpace S}
      (i : X ⟶ X') (i' : X' ⟶ X'')
      [AlgebraicGeometry.AlgebraicSpace.IsThickening i]
      [AlgebraicGeometry.AlgebraicSpace.IsThickening i'],
      AlgebraicGeometry.AlgebraicSpace.IsThickening (i ≫ i'))
