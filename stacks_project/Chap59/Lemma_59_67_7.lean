module

public import ReasLib.RingTheory.MvPolynomial.HomogeneousZeros
import StacksCheckRecall

@[expose] public section

universe u

namespace MvPolynomial

/- Lemma 59.67.7: over an algebraically closed field, fewer homogeneous
polynomials of positive degree than variables have a common nonzero zero. -/
@[stacks 03RB] #check (MvPolynomial.exists_common_nontrivialSolution :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    {n s : ℕ} (h_sn : s < n) (d : Fin s → ℕ) (h_degree : ∀ i, 0 < d i)
    (f : Fin s → MvPolynomial (Fin n) k)
    (h_homogeneous : ∀ i, (f i).IsHomogeneous (d i)),
    ∃ α : Fin n → k, α ≠ 0 ∧ ∀ i, MvPolynomial.eval α (f i) = 0)

end MvPolynomial
