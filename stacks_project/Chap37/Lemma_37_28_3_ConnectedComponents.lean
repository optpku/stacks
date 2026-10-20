/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ConnectedComponents

open CategoryTheory CategoryTheory.Limits

universe u

#check
  (AlgebraicGeometry.Scheme.Hom.geometricFiberComponentCount :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}}, (X ⟶ Y) → Y → ℕ∞)

#check
  (AlgebraicGeometry.Scheme.Hom.geometricFiberComponentCount_eq_enatCard :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (y : Y) (K : Type u)
      [Field K] [Algebra (Y.residueField y) K] [IsSepClosed K],
      f.geometricFiberComponentCount y =
        ENat.card
          (ConnectedComponents
            (AlgebraicGeometry.FieldExtension.baseChange (Y.residueField y) K
              (f.fiberToSpecResidueField y))))

#check
  (AlgebraicGeometry.Scheme.Hom.geometricFiberComponentCount_baseChange :
    ∀ {Y X Y' X' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g),
      f'.geometricFiberComponentCount =
        fun y' ↦ f.geometricFiberComponentCount (g y'))
