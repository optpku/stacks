/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Weil
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ClosedPoint

/-!
# Divisors associated with closed points

A closed point of a curve determines its reduced codimension-one prime divisor
and the coefficient-one Weil divisor supported there.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The reduced vanishing ideal of a closed point of a curve is an integral scheme. -/
theorem isIntegral_vanishingIdeal_closedPoint {k : Type u} [Field k]
    (X : SchemeOverField k) [Curve X] (x : X.left) (hx : x ∈ closedPoints X.left) :
    IsIntegral (vanishingIdeal ⟨({x} : Set X.left), hx⟩).subscheme := sorry

/-- The support of the reduced vanishing ideal of a closed point is irreducible. -/
theorem isIrreducible_support_vanishingIdeal_closedPoint {k : Type u} [Field k]
    (X : SchemeOverField k) [Curve X] (x : X.left) (hx : x ∈ closedPoints X.left) :
    IsIrreducible
      ((vanishingIdeal ⟨({x} : Set X.left), hx⟩).support : Set X.left) := sorry

/-- A closed point of a curve has codimension one. -/
theorem coheight_vanishingIdeal_closedPoint {k : Type u} [Field k]
    (X : SchemeOverField k) [Curve X] (x : X.left) (hx : x ∈ closedPoints X.left) :
    Order.coheight
      (⟨((vanishingIdeal ⟨({x} : Set X.left), hx⟩).support : Set X.left),
          isIrreducible_support_vanishingIdeal_closedPoint X x hx,
          (vanishingIdeal ⟨({x} : Set X.left), hx⟩).support.isClosed⟩ :
        TopologicalSpace.IrreducibleCloseds X.left) = 1 := sorry

/-- The prime divisor associated to a closed point of a curve. -/
def closedPointPrimeDivisor {k : Type u} [Field k]
    (X : SchemeOverField k) [Curve X] (x : X.left) (hx : x ∈ closedPoints X.left) :
    PrimeDivisor X.left :=
  PrimeDivisor.ofIdeal X.left (vanishingIdeal ⟨({x} : Set X.left), hx⟩)
    (isIntegral_vanishingIdeal_closedPoint X x hx)
    (isIrreducible_support_vanishingIdeal_closedPoint X x hx)
    (coheight_vanishingIdeal_closedPoint X x hx)

/-- The Weil divisor of a closed point of a curve. -/
def closedPointDivisor {k : Type u} [Field k]
    (X : SchemeOverField k) [Curve X] (x : X.left) (hx : x ∈ closedPoints X.left) :
    Div(X.left) :=
  WeilDivisor.single (closedPointPrimeDivisor X x hx)

/-- The closed-point divisor is the prime divisor of `{x}` with coefficient `1`. -/
theorem closedPointDivisor_spec {k : Type u} [Field k]
    (X : SchemeOverField k) [Curve X] (x : X.left) (hx : x ∈ closedPoints X.left) :
    (closedPointDivisor X x hx).coeff (closedPointPrimeDivisor X x hx) = 1 ∧
      (∀ Z : PrimeDivisor X.left, Z ≠ closedPointPrimeDivisor X x hx →
        (closedPointDivisor X x hx).coeff Z = 0) ∧
      ((closedPointPrimeDivisor X x hx).support : Set X.left) = {x} := sorry

end AlgebraicGeometry.Scheme
