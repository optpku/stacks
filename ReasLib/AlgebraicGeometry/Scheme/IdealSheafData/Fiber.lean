module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Fibers of closed subschemes

This file records when the closed subscheme associated to ideal-sheaf data is
disjoint from a scheme-theoretic fiber.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Ideal-sheaf data avoids the fiber of `p : Y ⟶ B` over `b` when its pullback to that
fiber defines the empty closed subscheme. -/
def avoidsFiber {Y B : Scheme.{u}} (p : Y ⟶ B) (Z : Y.IdealSheafData) (b : B) : Prop :=
  IsEmpty ((Z.comap (Scheme.Hom.fiberι p b)).subscheme)

end AlgebraicGeometry.Scheme.IdealSheafData
