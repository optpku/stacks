module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Principal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ClosedPoint

/-!
# Classical Riemann–Roch spaces of Weil divisors on curves

Effective Weil divisors, prime and closed-point divisors, and the spaces `L(D)`
and dimensions `l(D)` of rational functions with `(f) + D` effective.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

universe u

namespace AlgebraicGeometry.WeilDivisor

/-- A Weil divisor is effective when every prime coefficient is nonnegative. -/
def IsEffective {X : Scheme.{u}} (D : Div(X)) : Prop :=
  ∀ Z : PrimeDivisor X, 0 ≤ D.coeff Z

/-- Effectivity of a Weil divisor is nonnegativity of all prime coefficients. -/
theorem isEffective_iff {X : Scheme.{u}} (D : Div(X)) :
    IsEffective D ↔ ∀ Z : PrimeDivisor X, 0 ≤ D.coeff Z := sorry

/-- The zero Weil divisor is effective. -/
theorem isEffective_zero (X : Scheme.{u}) : IsEffective (0 : Div(X)) := sorry

/-- The sum of effective Weil divisors is effective. -/
theorem isEffective_add {X : Scheme.{u}} {D E : Div(X)}
    (hD : IsEffective D) (hE : IsEffective E) : IsEffective (D + E) := sorry

/-- The coefficient family of a prime Weil divisor is locally finite. -/
theorem locallyFinite_ofPrime {X : Scheme.{u}} (Z : PrimeDivisor X) :
    LocallyFinite fun W : PrimeDivisor X ↦
      if (@ite ℤ (W = Z) (Classical.propDecidable (W = Z)) 1 0) = 0 then
        (∅ : Set X)
      else
        (W.support : Set X) :=
  sorry

/-- The Weil divisor `[Z]` with coefficient `1` at a prime divisor and `0` elsewhere. -/
def ofPrime {X : Scheme.{u}} (Z : PrimeDivisor X) : Div(X) :=
  WeilDivisor.ofCoeff X
    (fun W ↦ @ite ℤ (W = Z) (Classical.propDecidable (W = Z)) 1 0)
    (locallyFinite_ofPrime Z)

/-- The coefficient of `[Z]` is `1` at `Z` and `0` at every other prime. -/
theorem coeff_ofPrime {X : Scheme.{u}} (Z W : PrimeDivisor X) :
    (ofPrime Z).coeff W =
      @ite ℤ (W = Z) (Classical.propDecidable (W = Z)) 1 0 := sorry

/-- A prime Weil divisor is nonzero. -/
theorem ofPrime_ne_zero {X : Scheme.{u}} (Z : PrimeDivisor X) : ofPrime Z ≠ 0 := sorry

/-- A prime Weil divisor is effective. -/
theorem isEffective_ofPrime {X : Scheme.{u}} (Z : PrimeDivisor X) :
    IsEffective (ofPrime Z) := sorry

end AlgebraicGeometry.WeilDivisor

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
  WeilDivisor.ofPrime (closedPointPrimeDivisor X x hx)

/-- The closed-point divisor is the prime divisor of `{x}` with coefficient `1`. -/
theorem closedPointDivisor_spec {k : Type u} [Field k]
    (X : SchemeOverField k) [Curve X] (x : X.left) (hx : x ∈ closedPoints X.left) :
    (closedPointDivisor X x hx).coeff (closedPointPrimeDivisor X x hx) = 1 ∧
      (∀ Z : PrimeDivisor X.left, Z ≠ closedPointPrimeDivisor X x hx →
        (closedPointDivisor X x hx).coeff Z = 0) ∧
      ((closedPointPrimeDivisor X x hx).support : Set X.left) = {x} := sorry

/-- The classical Riemann–Roch space `L(D)` of rational functions with `(f) + D`
effective, including zero. -/
def riemannRochSpace {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [IsLocallyNoetherian X.left] (D : Div(X.left)) :
    Set X.left.functionField :=
  {f | f = 0 ∨ ∃ hf : f ≠ 0,
    WeilDivisor.IsEffective (principalWeilDivisor X.left (Units.mk0 f hf) + D)}

/-- Membership in `L(D)` is vanishing or effectivity of `(f) + D`. -/
theorem mem_riemannRochSpace {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [IsLocallyNoetherian X.left] (D : Div(X.left))
    (f : X.left.functionField) :
    f ∈ riemannRochSpace X D ↔
      f = 0 ∨ ∃ hf : f ≠ 0,
        WeilDivisor.IsEffective (principalWeilDivisor X.left (Units.mk0 f hf) + D) :=
  sorry

/-- The zero function lies in every Riemann–Roch space. -/
theorem zero_mem_riemannRochSpace {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [IsLocallyNoetherian X.left] (D : Div(X.left)) :
    0 ∈ riemannRochSpace X D := sorry

/-- The dimension `l(D)` of the Riemann–Roch space as a `k`-vector space. -/
def riemannRochDim {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [IsLocallyNoetherian X.left] (D : Div(X.left)) : ℕ :=
  Module.finrank k
    (Submodule.span k
      (riemannRochSpace X D : Set (SchemeOverField.functionFieldCommAlg X)))

/-- `l(D)` is the `k`-rank of the span of `L(D)` in `k(X)`. -/
theorem riemannRochDim_eq_finrank {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [IsLocallyNoetherian X.left] (D : Div(X.left)) :
    riemannRochDim X D =
      Module.finrank k
        (Submodule.span k
          (riemannRochSpace X D : Set (SchemeOverField.functionFieldCommAlg X))) :=
  sorry

end AlgebraicGeometry.Scheme
