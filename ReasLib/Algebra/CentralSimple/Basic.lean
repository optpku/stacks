module

public import ReasLib.Algebra.CentralSimple.TwoSidedSubmodule
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Centrality transfer and tensor product simplicity

This file proves that finite-dimensional central simple algebras remain simple after tensoring
with any simple algebra. The key steps are:
- centrality descends from a matrix algebra to its coefficient division ring
- the tensor product of a central division algebra with a simple ring is simple (either order)
- a Wedderburn decomposition reduces the general case to the division-algebra case

## Main results

- `Algebra.IsCentral.of_matrix`: centrality of `Matrix (Fin n) (Fin n) K` implies centrality of `K`
- `IsSimpleRing.tensorProduct_of_central_division_right`: `K ⊗[k] A'` is simple
- `CSA.tensorProductMatrixEquiv`: tensor/matrix algebra equivalence
- `isSimpleRing_tensorProduct_of_finite_central_left_factor`: main simplicity theorem
- `isSimpleRing_tensorProduct_of_finite_central_factor`: symmetric corollary
-/

@[expose] public section

open Matrix
open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {A : Type v} {A' : Type w} [Ring A] [Ring A'] [Algebra k A] [Algebra k A']
variable [IsSimpleRing A] [IsSimpleRing A']

/-- Centrality of a matrix algebra descends to its division-ring coefficients. -/
theorem Algebra.IsCentral.of_matrix (n : ℕ) [NeZero n] (K : Type v) [DivisionRing K] [Algebra k K]
    [Algebra.IsCentral k (Matrix (Fin n) (Fin n) K)] :
    Algebra.IsCentral k K := by
  -- Pull the scalar matrix of a central element back to the corresponding diagonal entry.
  refine ⟨fun x hx ↦ ?_⟩
  have hxM : scalar (Fin n) x ∈ (Subalgebra.center k K).map (scalarAlgHom (Fin n) k) := by
    exact ⟨x, hx, rfl⟩
  rw [← subalgebraCenter_eq_scalarAlgHom_map] at hxM
  obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hxM
  rw [Algebra.mem_bot]
  refine ⟨a, ?_⟩
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  have := congrArg (fun M : Matrix (Fin n) (Fin n) K ↦ M i i) ha
  simp [Matrix.scalar_apply, i] at this
  exact this.symm

/-- The tensor product with a central division algebra is simple even when the division algebra
appears on the left. -/
theorem IsSimpleRing.tensorProduct_of_central_division_right
    {K : Type v} [DivisionRing K] [Algebra k K] [Algebra.IsCentral k K] :
    IsSimpleRing (K ⊗[k] A') := by
  -- Commute the factors to reuse the tensor-product simplicity theorem.
  let h : IsSimpleRing (A' ⊗[k] K) :=
    IsSimpleRing.tensorProduct_of_central_division (k := k) (A := A') (K := K)
  exact IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k A' K).toRingEquiv h

/-- Replacing the second coordinate of `Fin n × Fin 1` by zero fixes every pair. -/
lemma fin_prod_one_equiv_left_inv (n : ℕ) (ij : Fin n × Fin 1) : (ij.1, (0 : Fin 1)) = ij := by
  -- The second coordinate of `Fin 1` is forced, so the pair is determined by its first entry.
  rcases ij with ⟨i, j⟩
  have hj : j = 0 := Subsingleton.elim _ _
  simp [hj]

/-- Projection onto the first coordinate identifies `Fin n × Fin 1` with `Fin n`. -/
def fin_prod_one_equiv (n : ℕ) : Fin n × Fin 1 ≃ Fin n where
  toFun ij := ij.1
  invFun i := (i, 0)
  left_inv := fin_prod_one_equiv_left_inv n
  right_inv := fun _ ↦ rfl

/-- Tensoring a matrix presentation of `A` with `A'` yields a matrix presentation over
`K ⊗[k] A'`. -/
def CSA.tensorProductMatrixEquiv
    {n : ℕ} [NeZero n] {K : Type v} [DivisionRing K] [Algebra k K]
    (e : A ≃ₐ[k] Matrix (Fin n) (Fin n) K) :
    A ⊗[k] A' ≃ₐ[k] Matrix (Fin n) (Fin n) (K ⊗[k] A') :=
  let eA' : A' ≃ₐ[k] Matrix (Fin 1) (Fin 1) A' :=
    ((reindexAlgEquiv k A' finOneEquiv).trans uniqueAlgEquiv).symm
  let eTensor :
      A ⊗[k] A' ≃ₐ[k] Matrix (Fin n) (Fin n) K ⊗[k] Matrix (Fin 1) (Fin 1) A' :=
    Algebra.TensorProduct.congr e eA'
  let eKronecker :
      Matrix (Fin n) (Fin n) K ⊗[k] Matrix (Fin 1) (Fin 1) A' ≃ₐ[k]
        Matrix (Fin n × Fin 1) (Fin n × Fin 1) (K ⊗[k] A') :=
    Matrix.kroneckerTMulAlgEquiv (Fin n) (Fin 1) k k K A'
  -- First replace both factors by matrix models, then use the Kronecker tensor equivalence.
  eTensor.trans <| eKronecker.trans <| reindexAlgEquiv k (K ⊗[k] A') (fin_prod_one_equiv n)

/-- If `A` is a finite-dimensional central simple `k`-algebra and `A'` is simple over `k`, then
`A ⊗[k] A'` is simple. -/
theorem isSimpleRing_tensorProduct_of_finite_central_left_factor
    [FiniteDimensional k A] [Algebra.IsCentral k A] :
    IsSimpleRing (A ⊗[k] A') := by
  -- Follow the source proof through a Wedderburn matrix presentation of `A`.
  -- Local instance justification (proof-local temporary data): Wedderburn decomposition requires the Artinian property derived from finite dimensionality over k.
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn, K, hKdiv, hKalg, hKfinite, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  -- Local instance justification (noncanonical choice): the chosen Wedderburn presentation supplies its nonzero matrix size n.
  letI : NeZero n := hn
  -- Local instance justification (noncanonical choice): the chosen Wedderburn presentation supplies the division-ring structure on K.
  letI : DivisionRing K := hKdiv
  -- Local instance justification (noncanonical choice): the chosen Wedderburn presentation supplies the k-algebra structure on K.
  letI : Algebra k K := hKalg
  -- Local instance justification (proof-local temporary data): centrality of the chosen matrix presentation is transported along e before descending to K.
  letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) K) := Algebra.IsCentral.of_algEquiv k A _ e
  -- Local instance justification (proof-local temporary data): centrality of the chosen division algebra is obtained from its matrix presentation for the tensor simplicity theorem.
  letI : Algebra.IsCentral k K := Algebra.IsCentral.of_matrix (k := k) n K
  have hTensor : IsSimpleRing (K ⊗[k] A') :=
    IsSimpleRing.tensorProduct_of_central_division_right (k := k) (A' := A')
  have hMatrix : IsSimpleRing (Matrix (Fin n) (Fin n) (K ⊗[k] A')) :=
    IsSimpleRing.matrix (Fin n) (K ⊗[k] A')
  -- Transport simplicity back along the canonical tensor/matrix identification.
  exact IsSimpleRing.of_ringEquiv
    (CSA.tensorProductMatrixEquiv (k := k) (A := A) (A' := A') e).symm.toRingEquiv
    hMatrix

/-- If `A` and `A'` are simple `k`-algebras and one of them is finite-dimensional
and central over `k`, then the tensor product `A ⊗[k] A'` is simple. -/
theorem isSimpleRing_tensorProduct_of_finite_central_factor
    (h : (FiniteDimensional k A ∧ Algebra.IsCentral k A) ∨
      (FiniteDimensional k A' ∧ Algebra.IsCentral k A')) :
    IsSimpleRing (A ⊗[k] A') := by
  rcases h with h | h
  ·
    -- Local instance justification (proof-local temporary data): this disjunction branch supplies finite dimensionality of the left tensor factor A.
    letI := h.1
    -- Local instance justification (proof-local temporary data): this disjunction branch supplies centrality of the left tensor factor A.
    letI := h.2
    exact isSimpleRing_tensorProduct_of_finite_central_left_factor
  ·
    -- Local instance justification (proof-local temporary data): this disjunction branch supplies finite dimensionality of A' before commuting the tensor factors.
    letI := h.1
    -- Local instance justification (proof-local temporary data): this disjunction branch supplies centrality of A' before commuting the tensor factors.
    letI := h.2
    let h' : IsSimpleRing (A' ⊗[k] A) :=
      isSimpleRing_tensorProduct_of_finite_central_left_factor
    exact IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k A' A).toRingEquiv h'

end

end
