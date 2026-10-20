/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint
public import Mathlib.AlgebraicGeometry.Pullbacks

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

@[expose] public section

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {U X : Scheme.{u}}

/-- A lift of a geometric point `xbar` of `X` along a morphism `j : U ⟶ X`,
with the same source field as `xbar`. -/
structure Fiber (j : U ⟶ X) (xbar : GeometricPoint X) where
  /-- The scheme morphism `Spec k ⟶ U` lifting `xbar`. -/
  lift : Spec (.of xbar.K) ⟶ U
  /-- The lift composes with `j` to the morphism of `xbar`. -/
  fac : lift ≫ j = xbar.hom

namespace Fiber

variable {j : U ⟶ X} {xbar : GeometricPoint X}

/-- Construct a fiber point from a commuting lift of `xbar` along `j`. -/
def of (lift : Spec (.of xbar.K) ⟶ U) (fac : lift ≫ j = xbar.hom) :
    Fiber j xbar :=
  ⟨lift, fac⟩

/-- The underlying lift of `Fiber.of` is the supplied morphism. -/
theorem of_lift (lift : Spec (.of xbar.K) ⟶ U)
    (fac : lift ≫ j = xbar.hom) : (of lift fac).lift = lift := sorry

/-- The factorisation of `Fiber.of` is the supplied commuting square. -/
theorem of_fac (lift : Spec (.of xbar.K) ⟶ U)
    (fac : lift ≫ j = xbar.hom) : (of lift fac).fac = fac := sorry

/-- The geometric point of `U` associated to a lift of `xbar` along `j`. -/
def point (u : Fiber j xbar) : GeometricPoint U :=
  @GeometricPoint.of U xbar.K inferInstance xbar.isAlgClosed u.lift

/-- The scheme morphism of the associated geometric point is the chosen lift. -/
theorem point_hom (u : Fiber j xbar) : u.point.hom = u.lift := sorry

/-- Composing the associated geometric point of `U` with `j` recovers `xbar`. -/
theorem point_comp (u : Fiber j xbar) : u.point.hom ≫ j = xbar.hom := sorry

/-- Two lifts of the same geometric point with equal scheme morphisms are equal. -/
theorem ext {x y : Fiber j xbar} (h : x.lift = y.lift) : x = y := sorry

end Fiber

end AlgebraicGeometry.Scheme.GeometricPoint

namespace AlgebraicGeometry.Scheme.Hom

/-- The scheme-theoretic geometric fibre `ȳ ×_Y X` of `f` at a geometric point `ȳ` of `Y`. -/
noncomputable abbrev geometricFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ybar : GeometricPoint Y) : Scheme.{u} :=
  pullback ybar.hom f

/-- `geometricFiber` is the chosen fibre product `ȳ ×_Y X`. -/
theorem geometricFiber_def {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y) :
    geometricFiber f ybar = pullback ybar.hom f :=
  rfl

/-- The structure morphism `f' : ȳ ×_Y X ⟶ Spec κ(ȳ)` of the geometric fibre. -/
noncomputable abbrev geometricFiberToPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ybar : GeometricPoint Y) :
    geometricFiber f ybar ⟶ Spec (.of ybar.K) :=
  pullback.fst ybar.hom f

/-- `geometricFiberToPoint` is the first projection of `ȳ ×_Y X`. -/
theorem geometricFiberToPoint_def {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ybar : GeometricPoint Y) :
    geometricFiberToPoint f ybar = pullback.fst ybar.hom f :=
  rfl

/-- The base-change morphism `g' : ȳ ×_Y X ⟶ X` of the geometric fibre. -/
noncomputable abbrev geometricFiberToX {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ybar : GeometricPoint Y) :
    geometricFiber f ybar ⟶ X :=
  pullback.snd ybar.hom f

/-- `geometricFiberToX` is the second projection of `ȳ ×_Y X`. -/
theorem geometricFiberToX_def {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ybar : GeometricPoint Y) :
    geometricFiberToX f ybar = pullback.snd ybar.hom f :=
  rfl

/-- The geometric fibre with its projections forms a cartesian square over the original morphism. -/
theorem geometricFiber_isPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ybar : GeometricPoint Y) :
    IsPullback (geometricFiberToX f ybar) (geometricFiberToPoint f ybar) f ybar.hom :=
  (IsPullback.of_hasPullback ybar.hom f).flip

end AlgebraicGeometry.Scheme.Hom
