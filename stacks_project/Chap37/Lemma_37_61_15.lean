/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Perfect
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.61.15: if `i : Z ⟶ Y` and `j : Y ⟶ X` are immersions, `X` is locally
Noetherian, `i ≫ j` is a regular immersion, and `i` is perfect, then both `i` and `j`
are regular immersions. -/
@[stacks 09RK] #check
  (AlgebraicGeometry.regularImmersion_factors_of_perfect_of_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
      [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsImmersion i]
      [AlgebraicGeometry.IsImmersion j] [AlgebraicGeometry.IsRegularImmersion (i ≫ j)]
      [AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap i],
      AlgebraicGeometry.IsRegularImmersion i ∧ AlgebraicGeometry.IsRegularImmersion j)
