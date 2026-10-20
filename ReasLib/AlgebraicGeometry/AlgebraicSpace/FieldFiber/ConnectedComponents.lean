/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Connected.CardComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber

/-!
# Numbers of geometric connected components of fibres of algebraic spaces

The extended-natural-valued function `geometricFiberComponentCount f` counts
connected components of geometric fibres of a morphism of algebraic spaces. It
is independent of the algebraically closed representative of a point of `|Y|`
and is invariant under arbitrary base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The number of connected components of the geometric fibre of `f` at a
geometric point of the target. -/
noncomputable def geometricFiberComponentCountAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ybar : GeometricPoint Y) : ℕ∞ :=
  ENat.card (ConnectedComponents (Points (fieldFiber f ybar.toFieldValuedPoint)))

/-- The geometric fibre-component count at a geometric point depends only on the
image of that geometric point in `|Y|`. -/
theorem geometricFiberComponentCountAt_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ybar zbar : GeometricPoint Y) (h : ybar.image = zbar.image) :
    geometricFiberComponentCountAt f ybar = geometricFiberComponentCountAt f zbar :=
  sorry

/-- The function sending a point of `|Y|` to the number of connected components
of a geometric fibre of `f` over an algebraically closed representative of that
point. -/
noncomputable def geometricFiberComponentCount {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Points Y → ℕ∞ :=
  fun y ↦ geometricFiberComponentCountAt f (geometricPointOver y)

/-- Evaluating `geometricFiberComponentCount f` at `y` is the geometric
fibre-component count at the chosen geometric point over `y`. -/
theorem geometricFiberComponentCount_apply {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) :
    geometricFiberComponentCount f y =
      geometricFiberComponentCountAt f (geometricPointOver y) :=
  sorry

/-- The value of `geometricFiberComponentCount f` at `y` equals the number of
connected components of the fibre over any algebraically closed representative
of `y`. -/
theorem geometricFiberComponentCount_eq_enatCard {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) (ybar : GeometricPoint Y)
    (hy : ybar.image = y) :
    geometricFiberComponentCount f y =
      ENat.card
        (ConnectedComponents (Points (fieldFiber f ybar.toFieldValuedPoint))) :=
  sorry

/-- The geometric fibre-component count of a morphism of algebraic spaces is
invariant under arbitrary base change. -/
theorem geometricFiberComponentCount_baseChange {S : Scheme.{u}}
    {X Y Y' X' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (sq : IsPullback g' f' f g) :
    geometricFiberComponentCount f' =
      geometricFiberComponentCount f ∘ Points.map g :=
  sorry

/-- Evaluating the base-changed geometric fibre-component count at `y'` recovers
the original count at the image of `y'`. -/
theorem geometricFiberComponentCount_baseChange_apply {S : Scheme.{u}}
    {X Y Y' X' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (sq : IsPullback g' f' f g) (y' : Points Y') :
    geometricFiberComponentCount f' y' =
      geometricFiberComponentCount f (Points.map g y') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
