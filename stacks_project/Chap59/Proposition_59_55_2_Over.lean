/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Fiber

open CategoryTheory AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y)

/-- A geometric point of `X` over `ybar` with the same source field `ybar.K`. -/
abbrev Over := Fiber f ybar

/-- Construct a point of `X` over `ybar` from a factorization of `ybar.hom`. -/
def Over.of (toScheme : Spec (.of ybar.K) ⟶ X) (fac : toScheme ≫ f = ybar.hom) :
    Over f ybar :=
  Fiber.of toScheme fac

variable {f ybar}

/-- The morphism from the spectrum of the source field of a fiber point. -/
abbrev Over.toScheme (x : Over f ybar) : Spec (.of ybar.K) ⟶ X :=
  x.lift

/-- The geometric point of `X` associated to a point of `X` over `ybar`. -/
def Over.toGeometricPoint (x : Over f ybar) : GeometricPoint X :=
  x.point

/-- The scheme morphism of `toGeometricPoint` is the stored morphism to `X`. -/
theorem Over.toGeometricPoint_hom (x : Over f ybar) :
    x.toGeometricPoint.hom = x.toScheme :=
  rfl

/- Two points over the same geometric point with equal lifts are equal. -/
#check (Fiber.ext : ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} {ybar : GeometricPoint Y}
  {x y : Fiber f ybar}, x.lift = y.lift → x = y)

end AlgebraicGeometry.Scheme.GeometricPoint
