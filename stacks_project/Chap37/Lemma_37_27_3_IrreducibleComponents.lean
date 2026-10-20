/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.IrreducibleComponents

open CategoryTheory CategoryTheory.Limits

universe u

#check
  (AlgebraicGeometry.Scheme.Hom.geometricIrreducibleFiberComponentCount :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}}, (X ⟶ Y) → Y → ℕ∞)

#check
  (AlgebraicGeometry.Scheme.Hom.geometricIrreducibleFiberComponentCount_eq_enatCard :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (y : Y) (K : Type u)
      [Field K] [Algebra (Y.residueField y) K] [IsSepClosed K],
      f.geometricIrreducibleFiberComponentCount y =
        ENat.card
          (irreducibleComponents
            (AlgebraicGeometry.FieldExtension.baseChange (Y.residueField y) K
              (f.fiberToSpecResidueField y))))

#check
  (AlgebraicGeometry.Scheme.Hom.geometricIrreducibleFiberComponentCount_baseChange :
    ∀ {Y X Y' X' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g),
      f'.geometricIrreducibleFiberComponentCount =
        fun y' ↦ f.geometricIrreducibleFiberComponentCount (g y'))
