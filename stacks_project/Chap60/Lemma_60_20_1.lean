module

public import ReasLib.RingTheory.DividedPowers.DeRham.Completion
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 60.20.1 (1): the augmented divided-power de Rham complex of
`P = A⟨x_i⟩` remains exact after tensoring with every `A`-module. -/
@[stacks 07LC] #check (DPPolynomial.DeRham.coefficientComplex_acyclic :
  ∀ (A : Type u) [CommRing A] (ι : Type u) (M : Type u)
    [AddCommGroup M] [Module A M],
    (DPPolynomial.DeRham.coefficientComplex A ι M).Acyclic)

/- Lemma 60.20.1 (2): the p-adically completed divided-power de Rham complex of
`D` remains exact after completed tensoring with every p-adically complete `A`-module. -/
@[stacks 07LC] #check (DPPolynomial.DeRham.completedCoefficientComplex_acyclic :
  ∀ (A : Type u) [CommRing A] (ι : Type u) (p : ℕ) [Fact (Nat.Prime p)]
    (M : Type u) [AddCommGroup M] [Module A M]
    [IsAdicComplete (DPPolynomial.DeRham.principalIdealA A p) M],
    (DPPolynomial.DeRham.completedCoefficientComplex A ι p M).Acyclic)
