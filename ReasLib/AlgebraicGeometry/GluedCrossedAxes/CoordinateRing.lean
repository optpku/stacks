/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Coordinate algebra of crossed axes

The quotient `k[x, y] / (x * y)` maps to `k[T, T⁻¹] × k[T, T⁻¹]` through
positive and inverse coordinates. Evaluation at the origin and restriction to
each axis give the distinguished quotient algebra maps.
-/

@[expose] public section

noncomputable section

open MvPolynomial

universe u

namespace AlgebraicGeometry.GluedCrossedAxes

/-- The crossed-axes equation `X 0 * X 1` in `k[x, y]`. -/
def relation (k : Type u) [Field k] : MvPolynomial (Fin 2) k :=
  X 0 * X 1

/-- The common coordinate ring `k[x, y] / (x * y)` of the two affine charts. -/
abbrev CoordinateRing (k : Type u) [Field k] : Type u :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span {relation k}

/-- The class of the first coordinate, corresponding to the first variable of each chart. -/
def coordX (k : Type u) [Field k] : CoordinateRing k :=
  Ideal.Quotient.mk (Ideal.span {relation k}) (X 0)

/-- The class of the second coordinate, corresponding to the second variable of each chart. -/
def coordY (k : Type u) [Field k] : CoordinateRing k :=
  Ideal.Quotient.mk (Ideal.span {relation k}) (X 1)

/-- The two coordinates satisfy the crossed-axes equation `coordX * coordY = 0`. -/
theorem coordX_mul_coordY (k : Type u) [Field k] :
    coordX k * coordY k = 0 := sorry

/-- The overlap ring `C = k[T, T⁻¹] × k[T, T⁻¹]`. -/
abbrev OverlapRing (k : Type u) [Field k] : Type u :=
  LaurentPolynomial k × LaurentPolynomial k

/-- Evaluation of polynomials at `(T, 0)` and `(0, T)` in the overlap ring. -/
def fromAEval (k : Type u) [Field k] :
    MvPolynomial (Fin 2) k →ₐ[k] OverlapRing k :=
  aeval fun i ↦
    if i = 0 then (LaurentPolynomial.T (R := k) 1, 0)
    else (0, LaurentPolynomial.T (R := k) 1)

/-- The crossed-axes equation lies in the kernel of `fromAEval`. -/
private theorem fromAEval_eq_zero_of_mem_span {k : Type u} [Field k]
    {p : MvPolynomial (Fin 2) k} (hp : p ∈ Ideal.span {relation k}) :
    fromAEval k p = 0 := sorry

/-- The `k`-algebra map `A ⟶ C` sending `x ↦ (T, 0)` and `y ↦ (0, T)`. -/
@[no_expose]
def fromA (k : Type u) [Field k] : CoordinateRing k →ₐ[k] OverlapRing k :=
  Ideal.Quotient.liftₐ (Ideal.span {relation k}) (fromAEval k)
    fun _ hp ↦ fromAEval_eq_zero_of_mem_span hp

/-- `fromA` sends `coordX` to `(T, 0)`. -/
theorem fromA_coordX (k : Type u) [Field k] :
    fromA k (coordX k) = (LaurentPolynomial.T (R := k) 1, 0) := sorry

/-- `fromA` sends `coordY` to `(0, T)`. -/
theorem fromA_coordY (k : Type u) [Field k] :
    fromA k (coordY k) = (0, LaurentPolynomial.T (R := k) 1) := sorry

/-- Evaluation of polynomials at `(T⁻¹, 0)` and `(0, T⁻¹)` in the overlap ring. -/
def fromBEval (k : Type u) [Field k] :
    MvPolynomial (Fin 2) k →ₐ[k] OverlapRing k :=
  aeval fun i ↦
    if i = 0 then (LaurentPolynomial.T (R := k) (-1), 0)
    else (0, LaurentPolynomial.T (R := k) (-1))

/-- The crossed-axes equation lies in the kernel of `fromBEval`. -/
private theorem fromBEval_eq_zero_of_mem_span {k : Type u} [Field k]
    {p : MvPolynomial (Fin 2) k} (hp : p ∈ Ideal.span {relation k}) :
    fromBEval k p = 0 := sorry

/-- The `k`-algebra map `B ⟶ C` sending `u ↦ (T⁻¹, 0)` and `v ↦ (0, T⁻¹)`. -/
@[no_expose]
def fromB (k : Type u) [Field k] : CoordinateRing k →ₐ[k] OverlapRing k :=
  Ideal.Quotient.liftₐ (Ideal.span {relation k}) (fromBEval k)
    fun _ hp ↦ fromBEval_eq_zero_of_mem_span hp

/-- `fromB` sends `coordX` to `(T⁻¹, 0)`. -/
theorem fromB_coordX (k : Type u) [Field k] :
    fromB k (coordX k) = (LaurentPolynomial.T (R := k) (-1), 0) := sorry

/-- `fromB` sends `coordY` to `(0, T⁻¹)`. -/
theorem fromB_coordY (k : Type u) [Field k] :
    fromB k (coordY k) = (0, LaurentPolynomial.T (R := k) (-1)) := sorry

/-- The image of `x + y` under `fromA` is a unit of `C`. -/
theorem fromA_map_add_isUnit (k : Type u) [Field k] :
    IsUnit (fromA k (coordX k + coordY k)) := sorry

/-- The image of `u + v` under `fromB` is a unit of `C`. -/
theorem fromB_map_add_isUnit (k : Type u) [Field k] :
    IsUnit (fromB k (coordX k + coordY k)) := sorry

/-- The induced map `A_{x + y} ⟶ C`. -/
def fromAAway (k : Type u) [Field k] :
    Localization.Away (coordX k + coordY k) →+* OverlapRing k :=
  Localization.awayLift (fromA k).toRingHom (coordX k + coordY k)
    (fromA_map_add_isUnit k)

/-- The induced map `B_{u + v} ⟶ C`. -/
def fromBAway (k : Type u) [Field k] :
    Localization.Away (coordX k + coordY k) →+* OverlapRing k :=
  Localization.awayLift (fromB k).toRingHom (coordX k + coordY k)
    (fromB_map_add_isUnit k)

/-- The induced map `A_{x + y} ⟶ C` is bijective. -/
theorem fromAAway_bijective (k : Type u) [Field k] :
    Function.Bijective (fromAAway k) := sorry

/-- The induced map `B_{u + v} ⟶ C` is bijective. -/
theorem fromBAway_bijective (k : Type u) [Field k] :
    Function.Bijective (fromBAway k) := sorry

/-- The crossed-axes equation lies in the kernel of evaluation at the origin. -/
private theorem originEval_eq_zero_of_mem_span {k : Type u} [Field k]
    {p : MvPolynomial (Fin 2) k} (hp : p ∈ Ideal.span {relation k}) :
    MvPolynomial.aeval (fun _ : Fin 2 ↦ (0 : k)) p = 0 := sorry

/-- Evaluation at the origin `(0, 0)` of the affine crossed axes. -/
@[no_expose]
def originEval (k : Type u) [Field k] : CoordinateRing k →ₐ[k] k :=
  Ideal.Quotient.liftₐ (Ideal.span {relation k})
    (MvPolynomial.aeval fun _ ↦ (0 : k))
    fun _ hp ↦ originEval_eq_zero_of_mem_span hp

/-- Evaluation at the origin sends `coordX` to `0`. -/
theorem originEval_coordX (k : Type u) [Field k] :
    originEval k (coordX k) = 0 := sorry

/-- Evaluation at the origin sends `coordY` to `0`. -/
theorem originEval_coordY (k : Type u) [Field k] :
    originEval k (coordY k) = 0 := sorry

/-- Evaluation of polynomials onto the `x`-axis, sending `x ↦ X 0` and `y ↦ 0`. -/
def xAxisEval (k : Type u) [Field k] :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (ULift.{u} (Fin 1)) k :=
  MvPolynomial.aeval fun i ↦
    if i = 0 then MvPolynomial.X (ULift.up (0 : Fin 1)) else 0

/-- The crossed-axes equation lies in the kernel of `xAxisEval`. -/
private theorem xAxisEval_eq_zero_of_mem_span {k : Type u} [Field k]
    {p : MvPolynomial (Fin 2) k} (hp : p ∈ Ideal.span {relation k}) :
    xAxisEval k p = 0 := sorry

/-- The closed immersion of the `x`-axis on the ring side. -/
@[no_expose]
def xAxisHom (k : Type u) [Field k] :
    CoordinateRing k →ₐ[k] MvPolynomial (ULift.{u} (Fin 1)) k :=
  Ideal.Quotient.liftₐ (Ideal.span {relation k}) (xAxisEval k)
    fun _ hp ↦ xAxisEval_eq_zero_of_mem_span hp

/-- `xAxisHom` sends `coordX` to the affine-line coordinate. -/
theorem xAxisHom_coordX (k : Type u) [Field k] :
    xAxisHom k (coordX k) = MvPolynomial.X (ULift.up (0 : Fin 1)) := sorry

/-- `xAxisHom` sends `coordY` to `0`. -/
theorem xAxisHom_coordY (k : Type u) [Field k] :
    xAxisHom k (coordY k) = 0 := sorry

/-- Evaluation of polynomials onto the `y`-axis, sending `x ↦ 0` and `y ↦ X 0`. -/
def yAxisEval (k : Type u) [Field k] :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (ULift.{u} (Fin 1)) k :=
  MvPolynomial.aeval fun i ↦
    if i = 0 then 0 else MvPolynomial.X (ULift.up (0 : Fin 1))

/-- The crossed-axes equation lies in the kernel of `yAxisEval`. -/
private theorem yAxisEval_eq_zero_of_mem_span {k : Type u} [Field k]
    {p : MvPolynomial (Fin 2) k} (hp : p ∈ Ideal.span {relation k}) :
    yAxisEval k p = 0 := sorry

/-- The closed immersion of the `y`-axis on the ring side. -/
@[no_expose]
def yAxisHom (k : Type u) [Field k] :
    CoordinateRing k →ₐ[k] MvPolynomial (ULift.{u} (Fin 1)) k :=
  Ideal.Quotient.liftₐ (Ideal.span {relation k}) (yAxisEval k)
    fun _ hp ↦ yAxisEval_eq_zero_of_mem_span hp

/-- `yAxisHom` sends `coordX` to `0`. -/
theorem yAxisHom_coordX (k : Type u) [Field k] :
    yAxisHom k (coordX k) = 0 := sorry

/-- `yAxisHom` sends `coordY` to the affine-line coordinate. -/
theorem yAxisHom_coordY (k : Type u) [Field k] :
    yAxisHom k (coordY k) = MvPolynomial.X (ULift.up (0 : Fin 1)) := sorry

end AlgebraicGeometry.GluedCrossedAxes
