/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ConnectedComponents

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.28.3 (1): the number of connected components of a geometric fibre
can be computed after any separably closed extension of the residue field. -/
@[stacks 055F] #check
  (AlgebraicGeometry.Scheme.Hom.geometricFiberComponentCount_eq_enatCard :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (y : Y) (K : Type u)
      [Field K] [Algebra (Y.residueField y) K] [IsSepClosed K],
      f.geometricFiberComponentCount y =
        ENat.card
          (ConnectedComponents
            (AlgebraicGeometry.FieldExtension.baseChange (Y.residueField y) K
              (f.fiberToSpecResidueField y))))

/- Lemma 37.28.3 (2): the number of geometric connected components of the
fibres of a scheme morphism is invariant under arbitrary base change. -/
@[stacks 055F] #check
  (AlgebraicGeometry.Scheme.Hom.geometricFiberComponentCount_baseChange :
    ∀ {Y X Y' X' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g),
      f'.geometricFiberComponentCount =
        fun y' ↦ f.geometricFiberComponentCount (g y'))
