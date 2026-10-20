/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Cover.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 106.10.1. For a quasi-compact, quasi-separated algebraic space `Y`, a
quasi-compact open `V`, and a surjective flat locally-of-finite-presentation
morphism `f : X ⟶ V`, there exists a finite surjective cover of `Y` whose
inverse-image projection to `V` factors Zariski locally through `f`. -/
@[stacks 0CQ6] #check
  (AlgebraicGeometry.AlgebraicStack.exists_isFinite_surjective_zariskiLocallyFactorsThrough :
    ∀ {S : Scheme.{u}} (Y : AlgebraicSpace S)
      [AlgebraicSpace.IsQuasiCompact Y]
      [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
      (V : AlgebraicSpace.OpenSubspace Y) [AlgebraicSpace.IsQuasiCompact V.X]
      {X : GroupoidsOver S} [AlgebraicStack X] (f : X ⟶ V.X.toGroupoids)
      [AlgebraicStack.Surjective f] [AlgebraicStack.Flat f]
      [AlgebraicStack.LocallyOfFinitePresentation f],
      ∃ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y),
        AlgebraicSpace.IsFinite g ∧ AlgebraicSpace.Surjective g ∧
          AlgebraicStack.zariskiLocallyFactorsThrough (AlgebraicSpace.restrictTo g V) f)
