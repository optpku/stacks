module

public import ReasLib.RingTheory.MvPolynomial.TwoVectors
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.64.6 (Two vectors) (1): the residue-dependence locus over `ℤ` is closed. -/
@[stacks 0GRY] #check
  (MvPolynomial.TwoVectors.isClosed_dependentLocus_int :
    IsClosed (MvPolynomial.TwoVectors.dependentLocus ℤ))

/- Exercise 111.64.6 (Two vectors) (2): the residue-dependence locus over `ℤ` has
 topological Krull dimension `5`. -/
@[stacks 0GRY] #check
  (MvPolynomial.TwoVectors.topologicalKrullDim_dependentLocus :
    topologicalKrullDim (MvPolynomial.TwoVectors.dependentLocus ℤ) = 5)

/- Exercise 111.64.6 (Two vectors) (3): over every field the residue-dependence locus
has topological Krull dimension `4`. -/
@[stacks 0GRY] #check
  (MvPolynomial.TwoVectors.topologicalKrullDim_dependentLocus_field :
    ∀ {k : Type u} [Field k],
      topologicalKrullDim (MvPolynomial.TwoVectors.dependentLocus k) = 4)
