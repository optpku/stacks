/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.MatrixProduct
import StacksCheckRecall

/-!
Irreducible components of the `2 × 2` matrix-product locus as closed subsets of
`Spec(A)`, for `A` the ambient polynomial ring on the entries of `(X, Y)`.
-/

@[expose] public section

universe u

noncomputable section

/- Exercise 111.16.5 -/
@[stacks 02DR]
#check (MvPolynomial.MatrixProduct.zeroLocus_irreducibleComponents :
  ∀ (k : Type u) [Field k],
    {Z : Set (PrimeSpectrum (MvPolynomial (Fin 2 × Fin 2 × Fin 2) k)) |
        Maximal (fun W ↦ W ⊆
          PrimeSpectrum.zeroLocus (MvPolynomial.MatrixProduct.coordinateRingIdeal k) ∧
          IsClosed W ∧ IsIrreducible W) Z} =
      {PrimeSpectrum.zeroLocus (MvPolynomial.MatrixProduct.ambientYIdeal k),
        PrimeSpectrum.zeroLocus
          (MvPolynomial.MatrixProduct.ambientDeterminantIdeal k),
        PrimeSpectrum.zeroLocus (MvPolynomial.MatrixProduct.ambientXIdeal k)})

/- The product-relation zero locus is the union of the three ambient matrix-product loci. -/
#check (MvPolynomial.MatrixProduct.zeroLocus_eq_union :
  ∀ (k : Type u) [Field k],
    (PrimeSpectrum.zeroLocus (MvPolynomial.MatrixProduct.coordinateRingIdeal k) :
        Set (PrimeSpectrum (MvPolynomial (Fin 2 × Fin 2 × Fin 2) k))) =
      PrimeSpectrum.zeroLocus (MvPolynomial.MatrixProduct.ambientYIdeal k) ∪
        PrimeSpectrum.zeroLocus
          (MvPolynomial.MatrixProduct.ambientDeterminantIdeal k) ∪
        PrimeSpectrum.zeroLocus (MvPolynomial.MatrixProduct.ambientXIdeal k))
