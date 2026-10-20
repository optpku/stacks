/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyNoetherianFibers

/-!
# Base change of Cohen--Macaulay morphisms

This file records pointwise ascent and descent of Cohen--Macaulayness in a
cartesian square of scheme morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt

/-- Cohen--Macaulayness at a point ascends through a locally finite-type base
change when the original morphism has locally Noetherian fibres. -/
theorem pullback_of_isPullback
    {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    (h_fibers : LocallyNoetherianFibers f) [LocallyOfFiniteType g]
    (x' : X') (hcm : f.CohenMacaulayAt (g' x')) :
    f'.CohenMacaulayAt x' := sorry

/-- Cohen--Macaulayness at a point descends from a base change when the
original morphism is flat at the corresponding point. -/
theorem of_isPullback_of_flatAt
    {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    (h_fibers : LocallyNoetherianFibers f) [LocallyOfFiniteType g]
    (x' : X') (hflat : f.flatAt (g' x'))
    (hcm : f'.CohenMacaulayAt x') :
    f.CohenMacaulayAt (g' x') := sorry

/-- Cohen--Macaulayness at a point descends from a base change when the base
morphism is flat at the image of that point. -/
theorem of_isPullback_of_flatAt_base
    {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    (h_fibers : LocallyNoetherianFibers f) [LocallyOfFiniteType g]
    (x' : X') (hflat : g.flatAt (f' x'))
    (hcm : f'.CohenMacaulayAt x') :
    f.CohenMacaulayAt (g' x') := sorry

end AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt
