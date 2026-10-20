/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import ReasLib.NumberTheory.Automorphic.RamifiedHecke
public import ReasLib.NumberTheory.Automorphic.GaloisRepresentation

/-!
# Satake eigenvalues and ramified Frobenius attachment
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory Matrix
open Finset TopologicalSpace
open scoped RestrictedProduct

universe u v

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]

/-- The Satake/Hecke eigenvalue package of a `GL (Fin n)` eigenform on the open
`U`, recording the eigenvalues of `T_{v,i}` for `i = 1, …, n`. -/
structure EigenformGL (n : ℕ) (U : X.left.Opens) (Λ : Type v) [CommRing Λ] where
  /-- The Hecke eigenvalues of the operators `T_{v,i}` for
  `i = 1, …, n`. -/
  eigenvalue : closedPoints (restrictOpen X U).left → Fin n → Λ

namespace EigenformGL

variable {X}
variable {n : ℕ} {U : X.left.Opens} {Λ : Type v} [CommRing Λ]

/-- The eigenvalue system with the given eigenvalue family. -/
def of (eigenvalue : closedPoints (restrictOpen X U).left → Fin n → Λ) :
    EigenformGL X n U Λ where
  eigenvalue := eigenvalue

/-- The eigenvalue family of `of` is the given family. -/
theorem eigenvalue_apply
    (eigenvalue : closedPoints (restrictOpen X U).left → Fin n → Λ) :
    (of eigenvalue).eigenvalue = eigenvalue := sorry

/-- An eigenvalue system is recovered from its eigenvalue family. -/
theorem spec (f : EigenformGL X n U Λ) : f = of f.eigenvalue := sorry

/-- The extended Satake eigenvalues, with `lambda v 0 = 1`. -/
def lambda (f : EigenformGL X n U Λ)
    (v : closedPoints (restrictOpen X U).left) : Fin (n + 1) → Λ :=
  Fin.cases 1 fun j ↦ f.eigenvalue v j

/-- The zeroth Satake eigenvalue is `1`. -/
theorem lambda_zero (f : EigenformGL X n U Λ)
    (v : closedPoints (restrictOpen X U).left) :
    lambda f v 0 = 1 := sorry

end EigenformGL

/-- The Satake polynomial
`∑ i, (-1)^i q^{Nat.choose i 2} * lam i * X^{n-i}` attached to a family of Hecke
eigenvalues. -/
def satakeCharpoly (n : ℕ) {Λ : Type v} [CommRing Λ]
    (q : ℕ) (lam : Fin (n + 1) → Λ) : Polynomial Λ :=
  ∑ i : Fin (n + 1),
    Polynomial.C ((-1 : Λ) ^ (i : ℕ) * (q : Λ) ^ Nat.choose (i : ℕ) 2 * lam i) *
      Polynomial.X ^ (n - (i : ℕ))

/-- Unfolding of `satakeCharpoly` as the displayed finite sum. -/
theorem satakeCharpoly_apply (n : ℕ) {Λ : Type v} [CommRing Λ]
    (q : ℕ) (lam : Fin (n + 1) → Λ) :
    satakeCharpoly n q lam =
      ∑ i : Fin (n + 1),
        Polynomial.C ((-1 : Λ) ^ (i : ℕ) * (q : Λ) ^ Nat.choose (i : ℕ) 2 * lam i) *
          Polynomial.X ^ (n - (i : ℕ)) := sorry

/-- For `n = 2`, the Satake polynomial of the `heckeT`/`heckeU` eigenvalues
`(t, u)` is `X^2 - t X + q * u`. -/
theorem satakeCharpoly_two {Λ : Type v} [CommRing Λ] (q : ℕ) (t u : Λ) :
    satakeCharpoly 2 q (Fin.cases 1 fun j : Fin 2 ↦ if j.val = 0 then t else u) =
      Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X +
        Polynomial.C ((q : Λ) * u) := sorry

namespace EigenformGL

variable {X}
variable {n : ℕ} {U : X.left.Opens} {Λ : Type v} [CommRing Λ]
/-- The Satake polynomial of `f` at a closed point of `U`. -/
def charpoly [Finite k] (f : EigenformGL X n U Λ)
    (v : closedPoints (restrictOpen X U).left) : Polynomial Λ :=
  satakeCharpoly n (residueCard (restrictOpen X U) v) (lambda f v)

/-- The Satake polynomial of `f` is `satakeCharpoly` of its extended
eigenvalues. -/
theorem charpoly_apply [Finite k] (f : EigenformGL X n U Λ)
    (v : closedPoints (restrictOpen X U).left) :
    charpoly f v =
      satakeCharpoly n (residueCard (restrictOpen X U) v) (lambda f v) :=
  sorry

/-- Each Satake polynomial is monic. -/
theorem charpoly_monic [Finite k] (f : EigenformGL X n U Λ)
    (v : closedPoints (restrictOpen X U).left) :
    (charpoly f v).Monic := sorry

/-- Each Satake polynomial has natural degree `n`. -/
theorem natDegree_charpoly [Nontrivial Λ] [Finite k] (f : EigenformGL X n U Λ)
    (v : closedPoints (restrictOpen X U).left) :
    (charpoly f v).natDegree = n := sorry

/-- The last Satake eigenvalue `lambda v (Fin.last n)` is a unit of the valuation
ring of `PadicAlgCl ℓ`, equivalently
`(PadicAlgCl.valued ℓ).v (lambda v (Fin.last n)) = 1`. -/
def lambda_last_is_integral_unit {ℓ : ℕ} [Fact ℓ.Prime]
    (f : EigenformGL X n U (PadicAlgCl ℓ)) : Prop :=
  ∀ v, (PadicAlgCl.valued ℓ).v (lambda f v (Fin.last n)) = 1

/-- Unfolding of last-eigenvalue integrality as valuation exactly `1`. -/
theorem lambda_last_is_integral_unit_iff {ℓ : ℕ} [Fact ℓ.Prime]
    (f : EigenformGL X n U (PadicAlgCl ℓ)) :
    lambda_last_is_integral_unit f ↔
      ∀ v, (PadicAlgCl.valued ℓ).v (lambda f v (Fin.last n)) = 1 := sorry

/-- Last-eigenvalue integrality is equivalent to multiplicative norm `1`. -/
theorem lambda_last_nnnorm_eq_one_iff {ℓ : ℕ} [Fact ℓ.Prime]
    (f : EigenformGL X n U (PadicAlgCl ℓ)) :
    lambda_last_is_integral_unit f ↔
      ∀ v, ‖lambda f v (Fin.last n)‖₊ = 1 := sorry

/-- An eigenform `f` with values in `PadicAlgCl ℓ` is attached to a continuous
`GL (Fin n)`-valued representation `ρ` of `π₁(U)` when Satake polynomials match
geometric Frobenius characteristic polynomials after `Polynomial.map` to
`PadicAlgCl ℓ`. -/
def IsAttachedTo [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
    {xbar : GeometricPoint (restrictOpen X U).left}
    [ConnectedSpace (restrictOpen X U).left]
    {E : Type v} [Field E] [Algebra E (PadicAlgCl ℓ)] [TopologicalSpace E]
    (f : EigenformGL X n U (PadicAlgCl ℓ))
    (ρ : etaleFundamentalGroup (restrictOpen X U).left xbar →ₜ*
      GL (Fin n) E) : Prop :=
  ∀ (v : closedPoints (restrictOpen X U).left)
    (ι : GeometricPoint.finiteFiber
        (geometricPointOverClosedPoint (restrictOpen X U) v) ≅
      GeometricPoint.finiteFiber xbar),
    Polynomial.map (algebraMap E (PadicAlgCl ℓ))
        (Matrix.charpoly
          (ρ (etaleGeometricFrobenius (restrictOpen X U) xbar v ι)).val) =
      f.charpoly v

/-- Unfolding of attachment as matching of Satake and Frobenius
characteristic polynomials. -/
theorem isAttachedTo_iff [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
    {xbar : GeometricPoint (restrictOpen X U).left}
    [ConnectedSpace (restrictOpen X U).left]
    {E : Type v} [Field E] [Algebra E (PadicAlgCl ℓ)] [TopologicalSpace E]
    (f : EigenformGL X n U (PadicAlgCl ℓ))
    (ρ : etaleFundamentalGroup (restrictOpen X U).left xbar →ₜ*
      GL (Fin n) E) :
    f.IsAttachedTo ρ ↔
      ∀ (v : closedPoints (restrictOpen X U).left)
        (ι : GeometricPoint.finiteFiber
            (geometricPointOverClosedPoint (restrictOpen X U) v) ≅
          GeometricPoint.finiteFiber xbar),
        Polynomial.map (algebraMap E (PadicAlgCl ℓ))
            (Matrix.charpoly
              (ρ (etaleGeometricFrobenius (restrictOpen X U) xbar v ι)).val) =
          f.charpoly v := sorry

/-- Attached eigenforms recover Satake polynomials as mapped Frobenius
characteristic polynomials. -/
theorem isAttachedTo_charpoly [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
    {xbar : GeometricPoint (restrictOpen X U).left}
    [ConnectedSpace (restrictOpen X U).left]
    {E : Type v} [Field E] [Algebra E (PadicAlgCl ℓ)] [TopologicalSpace E]
    {f : EigenformGL X n U (PadicAlgCl ℓ)}
    {ρ : etaleFundamentalGroup (restrictOpen X U).left xbar →ₜ*
      GL (Fin n) E}
    (hf : f.IsAttachedTo ρ) (v : closedPoints (restrictOpen X U).left)
    (ι : GeometricPoint.finiteFiber
        (geometricPointOverClosedPoint (restrictOpen X U) v) ≅
      GeometricPoint.finiteFiber xbar) :
    f.charpoly v =
      Polynomial.map (algebraMap E (PadicAlgCl ℓ))
        (Matrix.charpoly
          (ρ (etaleGeometricFrobenius (restrictOpen X U) xbar v ι)).val) :=
  sorry

end EigenformGL

/-- An unramified-on-`U` cusp form is a Hecke eigenform for the Satake package
`f` when some value is a unit and `T_{v, i} φ = CuspFormGL.smul (eigenvalue v i) φ` for `i = 1, …, n`. -/
def IsEigenformGL [Finite k] (n : ℕ) (U : X.left.Opens) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (f : EigenformGL X n U Λ) : Prop :=
  (∃ x, IsUnit (φ.toFun x)) ∧
    ∀ (v : closedPoints (restrictOpen X U).left) (i : Fin n),
      heckeTGL X n U v (i.val + 1) φ = CuspFormGL.smul (f.eigenvalue v i) φ

/-- Unfolding of the ramified `GL (Fin n)` eigenform predicate. -/
theorem isEigenformGL_iff [Finite k] (n : ℕ) (U : X.left.Opens) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (f : EigenformGL X n U Λ) :
    IsEigenformGL X n U φ f ↔
      (∃ x, IsUnit (φ.toFun x)) ∧
        ∀ (v : closedPoints (restrictOpen X U).left) (i : Fin n),
          heckeTGL X n U v (i.val + 1) φ =
            CuspFormGL.smul (f.eigenvalue v i) φ := sorry

/-- A ramified `GL (Fin n)` eigenform takes a unit value. -/
theorem isEigenformGL_isUnit [Finite k] (n : ℕ) (U : X.left.Opens) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (f : EigenformGL X n U Λ)
    (hφ : IsEigenformGL X n U φ f) : ∃ x, IsUnit (φ.toFun x) := sorry

/-- A ramified `GL (Fin n)` eigenform is a `T_{v,i}`-eigenvector with eigenvalue
`f.eigenvalue v i`. -/
theorem isEigenformGL_heckeTGL [Finite k] (n : ℕ) (U : X.left.Opens) {Λ : Type v} [CommRing Λ]
    (φ : CuspFormGL X n U Λ) (f : EigenformGL X n U Λ)
    (hφ : IsEigenformGL X n U φ f)
    (v : closedPoints (restrictOpen X U).left) (i : Fin n) :
    heckeTGL X n U v (i.val + 1) φ =
      CuspFormGL.smul (f.eigenvalue v i) φ := sorry
/-- The `n = 2` Satake polynomial of the `heckeT`/`heckeU` eigenvalues
`(t_v, u_v)` is `X^2 - t_v X + (residueCard v) * u_v`. Under
`Eigenform.IsAttachedTo` this equals `Matrix.charpoly (ρ F_v)`. -/
theorem isAttachedTo_satakeCharpoly [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
    [ConnectedSpace X.left]
    (xbar : GeometricPoint X.left)
    {E : Type u} [Field E] [Algebra E (PadicAlgCl ℓ)] [TopologicalSpace E]
    (f : Eigenform X (PadicAlgCl ℓ))
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* GL (Fin 2) E)
    (hf : f.IsAttachedTo ρ) (v : closedPoints X.left)
    (ι : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
      GeometricPoint.finiteFiber xbar) :
    Polynomial.map (algebraMap E (PadicAlgCl ℓ))
        (Matrix.charpoly (ρ (etaleGeometricFrobenius X xbar v ι)).val) =
      satakeCharpoly 2 (residueCard X v)
        (Fin.cases 1 fun j : Fin 2 ↦ if j.val = 0 then f.t v else (f.u v).val) :=
  sorry


end AlgebraicGeometry.SchemeOverField
