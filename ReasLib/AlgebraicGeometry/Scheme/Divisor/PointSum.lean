/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Point-sum Cartier divisors on curves

The effective divisor `x 1 + ⋯ + x r` on a curve, realized as the product of the
reduced vanishing ideals of a tuple of closed points.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

variable {k : Type u} [Field k]

/-- The effective divisor `x 1 + ⋯ + x r` on a curve, as the product of the reduced
vanishing ideals of the closed points `x i`. -/
noncomputable def pointSumDivisor (X : SchemeOverField k) [Curve X] {r : ℕ}
    (x : Fin r → X.left) (hx : ∀ i, x i ∈ closedPoints X.left) :
    X.left.IdealSheafData :=
  (Finset.univ : Finset (Fin r)).prod fun i ↦
    vanishingIdeal ⟨({x i} : Set X.left), hx i⟩

/-- Unfold the point-sum divisor as a finite product of closed-point vanishing ideals. -/
theorem pointSumDivisor_eq (X : SchemeOverField k) [Curve X] {r : ℕ}
    (x : Fin r → X.left) (hx : ∀ i, x i ∈ closedPoints X.left) :
    pointSumDivisor X x hx =
      (Finset.univ : Finset (Fin r)).prod fun i ↦
        vanishingIdeal ⟨({x i} : Set X.left), hx i⟩ :=
  rfl

/-- The point-sum divisor of a tuple of closed points on a smooth curve over an
algebraically closed field is an effective Cartier divisor. -/
instance instIsEffectiveCartierDivisor_pointSumDivisor
    [IsAlgClosed k] (X : SchemeOverField k) [Curve X] [Smooth X.hom]
    {r : ℕ} (x : Fin r → X.left) (hx : ∀ i, x i ∈ closedPoints X.left) :
    IsEffectiveCartierDivisor (pointSumDivisor X x hx).subschemeι :=
  sorry

end AlgebraicGeometry.Curve
