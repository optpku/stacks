/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Data.Matrix.Mul
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.DottedArrow
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Map

/-!
# Polynomial maps of affine space and their Jacobians

A family of polynomials determines a morphism `𝔸ⁿ_k ⟶ 𝔸ᵐ_k`. Its Jacobian matrix
evaluated at a closed `k`-point represents the induced map on relative tangent spaces
under their coordinate identifications.
-/

@[expose] public section

open CategoryTheory MvPolynomial
open scoped AlgebraicGeometry DualNumber

noncomputable section

universe u

namespace AlgebraicGeometry.AffineSpace

open Scheme.Hom

/-- Evaluate a polynomial in `n` variables on the standard coordinates of affine `n`-space
over `k`. -/
def evalOnCoords {k : Type u} [Field k] (n : ℕ) (p : MvPolynomial (Fin n) k) :
    Γ(𝔸(ULift.{u} (Fin n); Spec (.of k)), ⊤) :=
  eval₂
    (((𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)).appTop).hom.comp
      (Scheme.ΓSpecIso (.of k)).inv.hom)
    (fun i ↦ coord (Spec (.of k)) (ULift.up i)) p

/-- Evaluating the coordinate polynomial `X i` recovers the `i`-th affine coordinate. -/
theorem evalOnCoords_X {k : Type u} [Field k] (n : ℕ) (i : Fin n) :
    evalOnCoords n (X i) = coord (Spec (.of k)) (ULift.up i) := sorry

/-- The morphism `𝔸ⁿ_k ⟶ 𝔸ᵐ_k` over `Spec k` determined by a family of `m` polynomials in
`n` variables. -/
def homOfPolynomials {k : Type u} [Field k] {n m : ℕ}
    (F : Fin m → MvPolynomial (Fin n) k) :
    𝔸(ULift.{u} (Fin n); Spec (.of k)) ⟶ 𝔸(ULift.{u} (Fin m); Spec (.of k)) :=
  homOfVector (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) fun j ↦
    evalOnCoords n (F j.down)

/-- A polynomial morphism of affine spaces over `k` commutes with the structure morphisms
to `Spec k`. -/
theorem homOfPolynomials_over {k : Type u} [Field k] {n m : ℕ}
    (F : Fin m → MvPolynomial (Fin n) k) :
    homOfPolynomials F ≫ (𝔸(ULift.{u} (Fin m); Spec (.of k)) ↘ Spec (.of k)) =
      𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k) := sorry

/-- Pullback of the `j`-th target coordinate along `homOfPolynomials F` is evaluation of
`F j` on the source coordinates. -/
theorem homOfPolynomials_appTop_coord {k : Type u} [Field k] {n m : ℕ}
    (F : Fin m → MvPolynomial (Fin n) k) (j : Fin m) :
    (homOfPolynomials F).appTop (coord (Spec (.of k)) (ULift.up j)) =
      evalOnCoords n (F j) := sorry

/-- The Jacobian matrix `A = (∂Fⱼ/∂xᵢ)` of a polynomial family, with rows indexed by output
polynomials and columns indexed by input variables. -/
def jacobianMatrix {k : Type u} [Field k] {n m : ℕ}
    (F : Fin m → MvPolynomial (Fin n) k) :
    Matrix (Fin m) (Fin n) (MvPolynomial (Fin n) k) :=
  fun j i ↦ pderiv i (F j)

/-- An entry of `jacobianMatrix F` is the corresponding partial derivative. -/
theorem jacobianMatrix_apply {k : Type u} [Field k] {n m : ℕ}
    (F : Fin m → MvPolynomial (Fin n) k) (j : Fin m) (i : Fin n) :
    jacobianMatrix F j i = pderiv i (F j) := sorry

/-- The `k`-coordinates of a closed point of affine `n`-space over an algebraically closed
field, read off the associated `k`-point. -/
def coordsOfClosedPoint {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) : Fin n → k :=
  fun i ↦
    (Scheme.ΓSpecIso (.of k)).hom
      ((pointOfClosedPoint (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) x hx).appTop
        (coord (Spec (.of k)) (ULift.up i)))

/-- The `i`-th closed-point coordinate agrees with residue-field evaluation of the `i`-th
affine coordinate, transported along `residueFieldIsoBase`. -/
theorem coordsOfClosedPoint_spec {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) (i : Fin n) :
    (residueFieldIsoBase (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) x hx).hom
        ((𝔸(ULift.{u} (Fin n); Spec (.of k))).Γevaluation x
          (coord (Spec (.of k)) (ULift.up i))) =
      coordsOfClosedPoint hx i := sorry

/-- The value of the polynomial Jacobian matrix at a `k`-tuple. -/
def jacobianMatrixEval {k : Type u} [Field k] {n m : ℕ}
    (F : Fin m → MvPolynomial (Fin n) k) (a : Fin n → k) :
    Matrix (Fin m) (Fin n) k :=
  fun j i ↦ eval a (jacobianMatrix F j i)

/-- An entry of `jacobianMatrixEval F a` is evaluation of the corresponding partial
derivative at `a`. -/
theorem jacobianMatrixEval_apply {k : Type u} [Field k] {n m : ℕ}
    (F : Fin m → MvPolynomial (Fin n) k) (a : Fin n → k) (j : Fin m) (i : Fin n) :
    jacobianMatrixEval F a j i = eval a (pderiv i (F j)) := sorry

/-- Matrix-vector multiplication by `jacobianMatrixEval F a` is the summed action of the
evaluated partials. -/
theorem jacobianMatrixEval_mulVec {k : Type u} [Field k] {n m : ℕ}
    (F : Fin m → MvPolynomial (Fin n) k) (a : Fin n → k) (v : Fin n → k) (j : Fin m) :
    (jacobianMatrixEval F a).mulVec v j =
      ∑ i : Fin n, jacobianMatrixEval F a j i * v i := sorry

/-- Read the coordinate vector of a relative tangent vector of affine `n`-space at a closed
point, by evaluating the derivation on germs of the standard coordinates and transporting
along `residueFieldIsoBase`. -/
def coordsOfTangent {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x})
    (D : tangentSpaceAt (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) x) :
    Fin n → k :=
  fun i ↦
    (residueFieldIsoBase (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) x hx).hom
      (D ((𝔸(ULift.{u} (Fin n); Spec (.of k))).presheaf.Γgerm x
        (coord (Spec (.of k)) (ULift.up i))))

/-- `coordsOfTangent` evaluates the derivation on the germ of the `i`-th coordinate. -/
theorem coordsOfTangent_apply {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x})
    (D : tangentSpaceAt (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) x) (i : Fin n) :
    coordsOfTangent hx D i =
      (residueFieldIsoBase (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) x hx).hom
        (D ((𝔸(ULift.{u} (Fin n); Spec (.of k))).presheaf.Γgerm x
          (coord (Spec (.of k)) (ULift.up i)))) := sorry

/-- The morphism `Spec k[ε] ⟶ 𝔸ⁿ_k` with coordinates `aᵢ + vᵢ ε`. -/
def homOfDualNumberCoords {k : Type u} [Field k] (n : ℕ) (a v : Fin n → k) :
    Spec (CommRingCat.of (k[ε])) ⟶ 𝔸(ULift.{u} (Fin n); Spec (.of k)) :=
  homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k (k[ε])))) fun j ↦
    (Scheme.ΓSpecIso (.of (k[ε]))).inv (a j.down, v j.down)

/-- The ring homomorphism `k[ε] →+* κ(x)[ε]` induced by `residueFieldIsoBase` at a closed
point of affine space. -/
def dualNumberResidueFieldIso {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) :
    k[ε] →+* ((𝔸(ULift.{u} (Fin n); Spec (.of k))).residueField x)[ε] where
  toFun z :=
    let φ :=
      (residueFieldIsoBase (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) x hx).inv.hom
    (φ z.1, φ z.2)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Applying `dualNumberResidueFieldIso` acts coefficientwise by `residueFieldIsoBase.inv`. -/
theorem dualNumberResidueFieldIso_apply {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) (z : k[ε]) :
    dualNumberResidueFieldIso hx z =
      ((residueFieldIsoBase
          (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) x hx).inv.hom z.1,
        (residueFieldIsoBase
          (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) x hx).inv.hom z.2) := sorry

/-- The dual-number lift of a closed point of affine space in the direction of a coordinate
tangent vector. -/
def tangentDualNumberHom {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) (v : Fin n → k) :
    Spec (CommRingCat.of (((𝔸(ULift.{u} (Fin n); Spec (.of k))).residueField x)[ε])) ⟶
      𝔸(ULift.{u} (Fin n); Spec (.of k)) :=
  Spec.map (CommRingCat.ofHom (dualNumberResidueFieldIso hx)) ≫
    homOfDualNumberCoords n (coordsOfClosedPoint hx) v

/-- The dual-number lift of a closed point recovers the residue-field point inclusion. -/
theorem tangentDualNumberHom_closedPoint {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) (v : Fin n → k) :
    dualNumberPointInclusion x ≫ tangentDualNumberHom hx v =
      (𝔸(ULift.{u} (Fin n); Spec (.of k))).fromSpecResidueField x := sorry

/-- The dual-number lift of a closed point lies over the dual-number base point of the
structure morphism. -/
theorem tangentDualNumberHom_over {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) (v : Fin n → k) :
    tangentDualNumberHom hx v ≫
        (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) =
      dualNumberToBasePoint (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) x ≫
        (Spec (.of k)).fromSpecResidueField
          ((𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) x) := sorry

/-- Assemble a relative tangent vector of affine `n`-space at a closed point from a
coordinate vector, as the derivation associated to the dual-number displacement
`x + v ε`. -/
def tangentOfCoords {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) (v : Fin n → k) :
    tangentSpaceAt (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) x :=
  dottedTangentArrowEquiv (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) x
    ⟨tangentDualNumberHom hx v, tangentDualNumberHom_closedPoint hx v,
      tangentDualNumberHom_over hx v⟩

/-- Evaluating `tangentOfCoords v` on the germ of the `i`-th coordinate recovers `v i`. -/
theorem tangentOfCoords_apply {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) (v : Fin n → k) (i : Fin n) :
    coordsOfTangent hx (tangentOfCoords hx v) i = v i := sorry

/-- `coordsOfTangent` is a left inverse of `tangentOfCoords`. -/
theorem coordsOfTangent_tangentOfCoords {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) (v : Fin n → k) :
    coordsOfTangent hx (tangentOfCoords hx v) = v := sorry

/-- `tangentOfCoords` is a left inverse of `coordsOfTangent`. -/
theorem tangentOfCoords_coordsOfTangent {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x})
    (D : tangentSpaceAt (𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) x) :
    tangentOfCoords hx (coordsOfTangent hx D) = D := sorry

/-- Transport `tangentOfCoords hx v` along `homOfPolynomials_over` so it is a relative
tangent vector for the composite structure morphism
`homOfPolynomials F ≫ (𝔸(ULift (Fin m); Spec (.of k)) ↘ Spec (.of k))`. -/
def tangentOfCoords_comp {k : Type u} [Field k] [IsAlgClosed k] {n m : ℕ}
    (F : Fin m → MvPolynomial (Fin n) k)
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) (v : Fin n → k) :
    tangentSpaceAt
      (homOfPolynomials F ≫ (𝔸(ULift.{u} (Fin m); Spec (.of k)) ↘ Spec (.of k))) x :=
  (homOfPolynomials_over F).symm ▸ tangentOfCoords hx v

/-- A polynomial morphism of affine spaces over an algebraically closed field induces a
bijective residue-field map at every closed point. -/
theorem homOfPolynomials_residueFieldMap_bijective {k : Type u} [Field k] [IsAlgClosed k]
    {n m : ℕ} (F : Fin m → MvPolynomial (Fin n) k)
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) :
    Function.Bijective (residueFieldMap (homOfPolynomials F) x).hom := sorry

/-- The image of a closed point under a polynomial morphism of affine spaces over an
algebraically closed field is closed. -/
theorem homOfPolynomials_isClosed_apply {k : Type u} [Field k] [IsAlgClosed k] {n m : ℕ}
    (F : Fin m → MvPolynomial (Fin n) k)
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) :
    IsClosed {homOfPolynomials F x} := sorry

/-- The coordinates of `y = homOfPolynomials F x` are evaluation of `F` at the coordinates
of `x`. -/
theorem coordsOfClosedPoint_homOfPolynomials {k : Type u} [Field k] [IsAlgClosed k]
    {n m : ℕ} (F : Fin m → MvPolynomial (Fin n) k)
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) (j : Fin m) :
    coordsOfClosedPoint (homOfPolynomials_isClosed_apply F hx) j =
      eval (coordsOfClosedPoint hx) (F j) := sorry

/-- Over an algebraically closed field, the relative tangent map of a polynomial
morphism of affine spaces at a closed point is multiplication by the Jacobian matrix
evaluated at the coordinates of that point. -/
theorem tangentMap_eq_jacobian {k : Type u} [Field k] [IsAlgClosed k]
    (n m : ℕ) (F : Fin m → MvPolynomial (Fin n) k)
    {x : 𝔸(ULift.{u} (Fin n); Spec (.of k))} (hx : IsClosed {x}) (v : Fin n → k) :
    coordsOfTangent (homOfPolynomials_isClosed_apply F hx)
      (relativeTangentMapAt (homOfPolynomials F)
        (𝔸(ULift.{u} (Fin m); Spec (.of k)) ↘ Spec (.of k)) x
        (homOfPolynomials_residueFieldMap_bijective F hx) (tangentOfCoords_comp F hx v)) =
      (jacobianMatrixEval F (coordsOfClosedPoint hx)).mulVec v := sorry

end AlgebraicGeometry.AffineSpace
