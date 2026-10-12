/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import stacks_project.Chap10.Example_10_35_23.MatrixAmbientIdeals
import StacksCheckRecall

/-!
The rank-one parametrization of the determinant component in Example 10.35.23.

The parameter ring and its maps are concrete data. The surrounding declarations record the
source-facing properties needed to identify the spectral image.

@stack 00GF
-/

@[expose] public section

open Matrix MvPolynomial PrimeSpectrum

universe u

noncomputable section

section

variable (k : Type u) [Field k]

/-- Helper for Chap10 Example 10 35 23: a `2 × 2` matrix over a field with zero determinant is
an outer product of a column vector and a row vector. -/
theorem exists_outerProduct_of_det_fin_two_eq_zero
    {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 2) K)
    (hdet : A.det = 0) :
    ∃ u v : Fin 2 → K, ∀ i j, A i j = u i * v j := sorry

/-- Helper for Chap10 Example 10 35 23: a determinant-zero pair `X,Y` satisfying `XY = 0` is
represented by `X = u vᵀ` and `Y = (-v₁,v₀) zᵀ`. -/
theorem exists_matrixProductKernelParameters
    {K : Type*} [Field K] (X Y : Matrix (Fin 2) (Fin 2) K)
    (hXY : X * Y = 0) (hdetX : X.det = 0) (hdetY : Y.det = 0) :
    ∃ u v z : Fin 2 → K,
      (∀ i j, X i j = u i * v j) ∧
      (∀ j, Y 0 j = -v 1 * z j) ∧
      (∀ j, Y 1 j = v 0 * z j) := sorry

/-- Helper for Chap10 Example 10 35 23: the polynomial parameter ring with coordinates
`u₀,u₁,v₀,v₁,z₀,z₁` used for the rank-one stratum. -/
abbrev matrixProductRankOneParamRing :=
  MvPolynomial (Fin 3 × Fin 2) k

/-- Helper for Chap10 Example 10 35 23: the ambient polynomial map for the parametrization
`X = u vᵀ` and `Y = (-v₁,v₀) zᵀ`. -/
def matrixProductRankOneParamEval :
    MvPolynomial (Fin 2 × Fin 2 × Fin 2) k →+* matrixProductRankOneParamRing k :=
  MvPolynomial.eval₂Hom (C : k →+* matrixProductRankOneParamRing k) fun a ↦
    match a with
    | (0, i, j) => X ((0 : Fin 3), i) * X ((1 : Fin 3), j)
    | (1, 0, j) => -X ((1 : Fin 3), 1) * X ((2 : Fin 3), j)
    | (1, 1, j) => X ((1 : Fin 3), 0) * X ((2 : Fin 3), j)

/-- Helper for Chap10 Example 10 35 23: the rank-one parametrization kills the four entries of
the product `XY`, so it descends to the matrix-product quotient ring. -/
theorem matrixProductCoordinateRingIdeal_le_rankOneParamEval_ker :
    matrixProductCoordinateRingIdeal k ≤ RingHom.ker (matrixProductRankOneParamEval k) := sorry

/-- Helper for Chap10 Example 10 35 23: the descended rank-one parametrization from the
matrix-product coordinate ring. -/
def matrixProductRankOneParamHom :
    matrixProductCoordinateRing k →+* matrixProductRankOneParamRing k :=
  Ideal.Quotient.lift (matrixProductCoordinateRingIdeal k)
    (matrixProductRankOneParamEval k)
    (matrixProductCoordinateRingIdeal_le_rankOneParamEval_ker (k := k))

/-- Helper for Chap10 Example 10 35 23: under the parametrization the `X` entries are `uᵢvⱼ`. -/
theorem matrixProductRankOneParamHom_xEntry (i j : Fin 2) :
    matrixProductRankOneParamHom k ((matrixProductGenericMatrix k 0) i j) =
      X ((0 : Fin 3), i) * X ((1 : Fin 3), j) := sorry

/-- Helper for Chap10 Example 10 35 23: under the parametrization the first row of `Y` is
`-v₁ zⱼ`. -/
theorem matrixProductRankOneParamHom_yZeroEntry (j : Fin 2) :
    matrixProductRankOneParamHom k ((matrixProductGenericMatrix k 1) 0 j) =
      -X ((1 : Fin 3), 1) * X ((2 : Fin 3), j) := sorry

/-- Helper for Chap10 Example 10 35 23: under the parametrization the second row of `Y` is
`v₀ zⱼ`. -/
theorem matrixProductRankOneParamHom_yOneEntry (j : Fin 2) :
    matrixProductRankOneParamHom k ((matrixProductGenericMatrix k 1) 1 j) =
      X ((1 : Fin 3), 0) * X ((2 : Fin 3), j) := sorry

/-- Helper for Chap10 Example 10 35 23: the parametrized `X` matrix has determinant zero. -/
theorem matrixProductRankOneParamHom_detX :
    matrixProductRankOneParamHom k (matrixProductGenericMatrix k 0).det = 0 := sorry

/-- Helper for Chap10 Example 10 35 23: the parametrized `Y` matrix has determinant zero. -/
theorem matrixProductRankOneParamHom_detY :
    matrixProductRankOneParamHom k (matrixProductGenericMatrix k 1).det = 0 := sorry

/-- Helper for Chap10 Example 10 35 23: every point in the spectral image of the rank-one
parametrization lies in the determinant-zero component. -/
theorem matrixProductRankOneParam_range_subset_determinantZeroComponent :
    Set.range (PrimeSpectrum.comap (matrixProductRankOneParamHom k)) ⊆
      matrixProductDeterminantZeroComponent k := sorry

/-- Helper for Chap10 Example 10 35 23: in the matrix-product coordinate ring the two generic
matrices multiply to zero. -/
theorem matrixProductGenericMatrices_mul_eq_zero :
    matrixProductGenericMatrix k 0 * matrixProductGenericMatrix k 1 = 0 := sorry

/-- Helper for Chap10 Example 10 35 23: a determinant-component prime lifts to the parameter
space under the rank-one parametrization. -/
theorem matrixProductRankOneParam_lifts_residuePoint
    (p : PrimeSpectrum (matrixProductCoordinateRing k))
    (hp : p ∈ matrixProductDeterminantZeroComponent k) :
    ∃ q : PrimeSpectrum (matrixProductRankOneParamRing k),
      PrimeSpectrum.comap (matrixProductRankOneParamHom k) q = p := sorry

/-- Helper for Chap10 Example 10 35 23: the determinant-zero component is exactly the spectral
image of the rank-one parametrization. -/
theorem matrixProductRankOneParam_range_eq_determinantZeroComponent :
    Set.range (PrimeSpectrum.comap (matrixProductRankOneParamHom k)) =
      matrixProductDeterminantZeroComponent k := sorry

/-- Helper for Chap10 Example 10 35 23: the determinant-zero component is irreducible because it
is the image of the irreducible parameter affine space. -/
theorem matrixProductDeterminantZeroComponent_isIrreducible :
    IsIrreducible (matrixProductDeterminantZeroComponent k) := sorry

end

@[stacks 00GF "rank-one ambient evaluation"]
#check @matrixProductRankOneParamEval

@[stacks 00GF "rank-one quotient parametrization"]
#check @matrixProductRankOneParamHom

@[stacks 00GF "determinant component as spectral image"]
#check @matrixProductRankOneParam_range_eq_determinantZeroComponent

@[stacks 00GF "irreducibility of the determinant component"]
#check @matrixProductDeterminantZeroComponent_isIrreducible
