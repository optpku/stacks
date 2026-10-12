/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.StarIdeal
import StacksCheckRecall

/-!
# Exercise 111.58.4

Irreducible components of `zeroLocus (xy, xz, xw)` in
`Spec(MvPolynomial (Fin 4) k)`, and their topological Krull dimensions.
-/

@[expose] public section

universe u

noncomputable section

open MvPolynomial PrimeSpectrum

/- Exercise 111.58.4 (1): over a field `k`, the irreducible components of the zero locus of
`(X 0 * X 1, X 0 * X 2, X 0 * X 3)` are the hyperplane and axis zero loci. -/
@[stacks 0D5J] #check
  (MvPolynomial.StarIdeal.relationIdeal_irreducibleComponents :
    ∀ (k : Type u) [Field k],
      {Z : Set (PrimeSpectrum (MvPolynomial (Fin 4) k)) |
          Maximal (fun W ↦ W ⊆
            zeroLocus (MvPolynomial.StarIdeal.relationIdeal k : Set (MvPolynomial (Fin 4) k)) ∧
            IsClosed W ∧ IsIrreducible W) Z} =
        {zeroLocus (MvPolynomial.StarIdeal.hyperplanePrime k : Set (MvPolynomial (Fin 4) k)),
          zeroLocus (MvPolynomial.StarIdeal.axisPrime k : Set (MvPolynomial (Fin 4) k))})

/- Exercise 111.58.4 (2): the hyperplane component has topological Krull dimension `3`. -/
@[stacks 0D5J] #check
  (MvPolynomial.StarIdeal.topologicalKrullDim_zeroLocus_hyperplanePrime :
    ∀ (k : Type u) [Field k],
      topologicalKrullDim
          (zeroLocus (MvPolynomial.StarIdeal.hyperplanePrime k : Set (MvPolynomial (Fin 4) k))) = 3)

/- Exercise 111.58.4 (3): the axis component has topological Krull dimension `1`. -/
@[stacks 0D5J] #check
  (MvPolynomial.StarIdeal.topologicalKrullDim_zeroLocus_axisPrime :
    ∀ (k : Type u) [Field k],
      topologicalKrullDim
          (zeroLocus (MvPolynomial.StarIdeal.axisPrime k : Set (MvPolynomial (Fin 4) k))) = 1)
