/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.NumberTheory.FunctionField.Adele

/-! # Single-place adelic embeddings -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme Matrix
open scoped RestrictedProduct

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]

/-- A local element is a uniformizer when its valuation is `exp (-1)`. -/
def IsUniformizer (place : closedPoints X.left) (parameter : completion X place) : Prop :=
  Valued.v parameter = WithZero.exp (-1 : ℤ)

/-- The uniformizer condition is the valuation equality `v(parameter) = exp (-1)`. -/
theorem isUniformizer_iff (place : closedPoints X.left) (parameter : completion X place) :
    IsUniformizer X place parameter ↔ Valued.v parameter = WithZero.exp (-1 : ℤ) := sorry

/-- Closed points have classical decidable equality. -/
instance instDecidableEq_closedPoints : DecidableEq (closedPoints X.left) :=
  Classical.decEq _

/-- The adele with a prescribed component at one place and `1` elsewhere. -/
def localAdele (place : closedPoints X.left) (element : completion X place) : adeleRing X :=
  RestrictedProduct.mulSingle (fun other ↦ completionIntegers X other) place element

/-- The selected component of the multiplicative single-place embedding is the input. -/
theorem localAdele_apply_self (place : closedPoints X.left) (element : completion X place) :
    localAdele X place element place = element := sorry

/-- Every other component of the multiplicative single-place embedding is `1`. -/
theorem localAdele_apply_of_ne (place : closedPoints X.left) (element : completion X place)
    (other : closedPoints X.left) (h_ne : other ≠ place) :
    localAdele X place element other = 1 := sorry

/-- The adele with a prescribed component at one place and `0` elsewhere. -/
def localAdeleZero (place : closedPoints X.left) (element : completion X place) : adeleRing X :=
  RestrictedProduct.single (fun other ↦ completionIntegers X other) place element

/-- The selected component of the additive single-place embedding is the input. -/
theorem localAdeleZero_apply_self (place : closedPoints X.left) (element : completion X place) :
    localAdeleZero X place element place = element := sorry

/-- Every other component of the additive single-place embedding is `0`. -/
theorem localAdeleZero_apply_of_ne (place : closedPoints X.left) (element : completion X place)
    (other : closedPoints X.left) (h_ne : other ≠ place) :
    localAdeleZero X place element other = 0 := sorry

/-- The multiplicative single-place embedding is integral at all but finitely many places. -/
theorem localAdele_eventually (place : closedPoints X.left) (element : completion X place) :
    ∀ᶠ other : closedPoints X.left in Filter.cofinite,
      localAdele X place element other ∈ completionIntegers X other := sorry

/-- The additive single-place embedding is integral at all but finitely many places. -/
theorem localAdeleZero_eventually (place : closedPoints X.left) (element : completion X place) :
    ∀ᶠ other : closedPoints X.left in Filter.cofinite,
      localAdeleZero X place element other ∈ completionIntegers X other := sorry

/-- The single-place embeddings of a local unit and its inverse are mutual inverses. -/
theorem localAdeleUnit_inverse (place : closedPoints X.left) (unit : (completion X place)ˣ) :
    localAdele X place unit.val * localAdele X place unit.inv = 1 ∧
      localAdele X place unit.inv * localAdele X place unit.val = 1 := sorry

/-- The idèle with a prescribed local unit at one place and `1` elsewhere. -/
def localAdeleUnit (place : closedPoints X.left) (unit : (completion X place)ˣ) :
    (adeleRing X)ˣ where
  val := localAdele X place unit.val
  inv := localAdele X place unit.inv
  val_inv := (localAdeleUnit_inverse X place unit).1
  inv_val := (localAdeleUnit_inverse X place unit).2

/-- The underlying adele of the local unit embedding is its multiplicative embedding. -/
theorem localAdeleUnit_val (place : closedPoints X.left) (unit : (completion X place)ˣ) :
    (localAdeleUnit X place unit).val = localAdele X place unit.val := sorry

/-- Embed a local matrix as the identity matrix at every other place. -/
def localMatrix (place : closedPoints X.left)
    (matrix : Matrix (Fin 2) (Fin 2) (completion X place)) :
    Matrix (Fin 2) (Fin 2) (adeleRing X) :=
  fun row column ↦ if row = column then localAdele X place (matrix row column)
    else localAdeleZero X place (matrix row column)

/-- Diagonal entries use the multiplicative embedding and off-diagonal entries the additive one. -/
theorem localMatrix_apply (place : closedPoints X.left)
    (matrix : Matrix (Fin 2) (Fin 2) (completion X place)) (row column : Fin 2) :
    localMatrix X place matrix row column =
      if row = column then localAdele X place (matrix row column)
      else localAdeleZero X place (matrix row column) := sorry

/-- The embeddings of an invertible local matrix and its inverse are mutual inverses. -/
theorem localMatrix_inverse (place : closedPoints X.left)
    (matrix : GL (Fin 2) (completion X place)) :
    localMatrix X place matrix.val * localMatrix X place matrix.inv = 1 ∧
      localMatrix X place matrix.inv * localMatrix X place matrix.val = 1 := sorry

/-- Embed an invertible local matrix as the identity at every other place. -/
def localGL (place : closedPoints X.left) (matrix : GL (Fin 2) (completion X place)) :
    GL (Fin 2) (adeleRing X) where
  val := localMatrix X place matrix.val
  inv := localMatrix X place matrix.inv
  val_inv := (localMatrix_inverse X place matrix).1
  inv_val := (localMatrix_inverse X place matrix).2

/-- The underlying matrix of the local general linear group embedding is the local matrix embedding. -/
theorem localGL_val (place : closedPoints X.left) (matrix : GL (Fin 2) (completion X place)) :
    (localGL X place matrix).val = localMatrix X place matrix.val := sorry

end AlgebraicGeometry.SchemeOverField
