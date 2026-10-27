/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Base change of Cohen--Macaulay morphisms of algebraic spaces

Pointwise Cohen--Macaulayness ascends along locally finite-type base change
for morphisms with locally Noetherian fibres. It descends under pointwise
flatness of either the original morphism or the base morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohenMacaulayAt

/-- In a cartesian square of algebraic spaces, Cohen--Macaulayness at a point
ascends along a locally finite-type base change when the original morphism
has locally Noetherian fibres. -/
theorem pullback_of_isPullback {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hcm : CohenMacaulayAt f (Points.map g' x')) :
    CohenMacaulayAt f' x' :=
  sorry

/-- In a cartesian square of algebraic spaces, Cohen--Macaulayness at a point
descends along a locally finite-type base change when the original morphism
has locally Noetherian fibres and is flat at the image point. -/
theorem of_isPullback_of_flatAt {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hflat : FlatAt f (Points.map g' x'))
    (hcm : CohenMacaulayAt f' x') :
    CohenMacaulayAt f (Points.map g' x') :=
  sorry

/-- In a cartesian square of algebraic spaces, Cohen--Macaulayness at a point
descends along a locally finite-type base change when the original morphism
has locally Noetherian fibres and the base morphism is flat at the image of
the chosen point in the base-changed target. -/
theorem of_isPullback_of_flatAt_base {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hflat : FlatAt g (Points.map f' x'))
    (hcm : CohenMacaulayAt f' x') :
    CohenMacaulayAt f (Points.map g' x') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohenMacaulayAt
