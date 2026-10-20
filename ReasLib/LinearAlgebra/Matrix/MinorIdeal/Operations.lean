module

public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Order.Monotone.Basic
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Basic

@[expose] public section

/-!
# Operations on Determinantal Ideals

Reusable functoriality, monotonicity, and block-sum interfaces for matrix minor
ideals.

@stack 00N1
@stack 07Z7
-/

universe u v w x y

namespace Matrix

variable {R : Type u} [CommRing R]

/-- A determinant selected by an arbitrary row map belongs to the minor ideal:
noninjective row maps contribute the zero determinant. -/
theorem det_submatrix_mem_minorIdeal_of_rowMap {ι : Type v} {κ : Type w}
    (r : ℕ) (A : Matrix ι κ R) (f : Fin r → ι) (e₂ : Fin r ↪ κ) :
    (A.submatrix f e₂).det ∈ I_(r)(A) := sorry

/-- Increasing the minor size by one can only decrease the associated ideal. -/
theorem minorIdeal_succ_le {ι : Type v} {κ : Type w}
    (r : ℕ) (A : Matrix ι κ R) : I_((r + 1))(A) ≤ I_(r)(A) := sorry

/-- Minor ideals of a fixed matrix are antitone in the minor size. -/
@[stacks 07Z7 "(1), antitonicity of minor ideals"]
theorem minorIdeal_antitone {ι : Type v} {κ : Type w}
    (A : Matrix ι κ R) : Antitone (fun r ↦ I_(r)(A)) := sorry

/-- Deleting `n'` final rows makes the corresponding shifted minor ideal map
into the minor ideal of the remaining initial rows. -/
@[stacks 07Z7 "(2), initial-row minor bound"]
theorem minorIdeal_initialRows_le {n n' m : ℕ} (r : ℕ)
    (B : Matrix (Fin (n + n')) (Fin m) R) :
    I_((r + n'))(B) ≤ I_(r)((B.submatrix (Fin.castAdd n') id)) := sorry

/-- Each chosen minor of a left matrix product belongs to the minor ideal of the
right factor. -/
theorem det_submatrix_mul_left_mem_minorIdeal {ι : Type v} {κ : Type w} [Fintype ι]
    (r : ℕ) (C : Matrix ι ι R) (A : Matrix ι κ R)
    (e₁ : Fin r ↪ ι) (e₂ : Fin r ↪ κ) :
    ((C * A).submatrix e₁ e₂).det ∈ I_(r)(A) := sorry

/-- Left multiplication does not increase a matrix minor ideal. -/
@[stacks 07Z7 "(3), left multiplication of minor ideals"]
theorem minorIdeal_mul_left_le {ι : Type v} {κ : Type w} [Fintype ι]
    (r : ℕ) (C : Matrix ι ι R) (A : Matrix ι κ R) :
    I_(r)((C * A)) ≤ I_(r)(A) := sorry

/-- Transposing a matrix preserves each fixed-size minor ideal. -/
@[stacks 00N1 "minor ideals"]
theorem minorIdeal_transpose_eq {ι : Type v} {κ : Type w}
    (r : ℕ) (A : Matrix ι κ R) :
    I_(r)(A.transpose) = I_(r)(A) := sorry

/-- Right multiplication by a square matrix does not increase a fixed-size
minor ideal. -/
@[stacks 00N1 "minor ideals"]
theorem minorIdeal_mul_right_le {ι : Type v} {κ : Type w} [Fintype κ]
    (r : ℕ) (A : Matrix ι κ R) (C : Matrix κ κ R) :
    I_(r)((A * C)) ≤ I_(r)(A) := sorry

/-- The minor ideal of a block diagonal matrix is the antidiagonal sum of the
products of the minor ideals of its two diagonal blocks. -/
@[stacks 07Z7 "(4), block-diagonal minor formula"]
theorem minorIdeal_fromBlocks {ι₁ : Type v} {ι₂ : Type w} {κ₁ : Type x} {κ₂ : Type y}
    (r : ℕ) (A₁ : Matrix ι₁ κ₁ R) (A₂ : Matrix ι₂ κ₂ R) :
    I_(r)((fromBlocks A₁ 0 0 A₂)) =
      Finset.sum (Finset.antidiagonal r) fun p ↦ I_(p.1)(A₁) * I_(p.2)(A₂) := sorry

end Matrix
