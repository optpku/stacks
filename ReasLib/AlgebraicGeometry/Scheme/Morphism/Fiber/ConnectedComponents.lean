/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Connected.CardComponents
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.IsSepClosed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange

/-!
# Numbers of geometric connected components of fibres

This module defines the extended-natural-valued number of connected components
of a geometric fibre and records its independence and base-change properties.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The number of connected components of the geometric fibre of a morphism at
its point, computed over the canonical separable closure of the residue field. -/
noncomputable def geometricFiberComponentCount {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) : ℕ∞ :=
  ENat.card
    (ConnectedComponents
      (AlgebraicGeometry.FieldExtension.baseChange (Y.residueField y)
        (SeparableClosure (Y.residueField y)) (f.fiberToSpecResidueField y)))

/-- The number of geometric connected components of a fibre is unchanged by
base change to a separably closed extension of its residue field. -/
theorem geometricFiberComponentCount_eq_enatCard {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) (K : Type u) [Field K] [Algebra (Y.residueField y) K]
    [IsSepClosed K] :
    f.geometricFiberComponentCount y =
      ENat.card
        (ConnectedComponents
          (AlgebraicGeometry.FieldExtension.baseChange (Y.residueField y) K
            (f.fiberToSpecResidueField y))) := sorry

/-- The geometric fibre-component count is preserved by a pullback square of
scheme morphisms. -/
theorem geometricFiberComponentCount_baseChange {Y X Y' X' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) :
    f'.geometricFiberComponentCount =
      fun y' ↦ f.geometricFiberComponentCount (g y') := sorry

end AlgebraicGeometry.Scheme.Hom
