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

/- Lemma 37.61.15: under the stated hypotheses, `i` is regular and `j` is regular near
every point of the image of `i`. Global regularity of `j` requires image coverage, supplied
here by the explicit surjectivity hypothesis. -/
@[stacks 09RK] #check
  (AlgebraicGeometry.regularImmersion_factors_of_perfect_of_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
      [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsImmersion i]
      [AlgebraicGeometry.IsImmersion j] [AlgebraicGeometry.IsRegularImmersion (i ≫ j)]
      [AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap i]
      (hi : Function.Surjective i.base),
      AlgebraicGeometry.IsRegularImmersion i ∧ AlgebraicGeometry.IsRegularImmersion j)
