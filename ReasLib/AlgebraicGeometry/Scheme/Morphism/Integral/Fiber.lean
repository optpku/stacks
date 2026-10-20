/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ClosedPoint

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Every point of an integral scheme morphism is closed in the scheme-theoretic fibre over
its image. -/
theorem asFiber_mem_closedPoints_of_isIntegralHom
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegralHom f] (x : X) :
    f.asFiber x ∈ closedPoints (f.fiber (f x)) := sorry

end AlgebraicGeometry
