/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Effective
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Principal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ClosedPoint

/-!
# Classical Riemann–Roch spaces of Weil divisors on curves

The spaces `L(D)` and dimensions `l(D)` of rational functions with `(f) + D`
effective.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

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
        WeilDivisor.IsEffective (principalWeilDivisor X.left (Units.mk0 f hf) + D) := Iff.rfl

/-- The zero function lies in every Riemann–Roch space. -/
theorem zero_mem_riemannRochSpace {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [IsLocallyNoetherian X.left] (D : Div(X.left)) :
    0 ∈ riemannRochSpace X D := by
  exact Or.inl rfl

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
          (riemannRochSpace X D : Set (SchemeOverField.functionFieldCommAlg X))) := rfl

end AlgebraicGeometry.Scheme
