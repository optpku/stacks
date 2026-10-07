module

public import ReasLib.RingTheory.MvPolynomial.AlgebraicSet
import StacksCheckRecall

@[expose]
public section

universe u

namespace MvPolynomial

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

/- Exercise 111.15.1: an algebraic set in affine `n`-space over an algebraically
closed field can always be written as the zero locus of finitely many
polynomials. -/
@[stacks 0FJ4] #check (MvPolynomial.IsAlgebraicSet.exists_finset :
  ∀ {Z : Set (Fin n → k)}, IsAlgebraicSet Z →
    ∃ T : Finset (MvPolynomial (Fin n) k), Z = {x | ∀ p ∈ T, aeval x p = 0})

/- An algebraic set in affine `n`-space is the zero locus of the ideal spanned by
finitely many polynomials. -/
#check (MvPolynomial.IsAlgebraicSet.exists_finset_span :
  ∀ {Z : Set (Fin n → k)}, IsAlgebraicSet Z →
    ∃ T : Finset (MvPolynomial (Fin n) k),
      Z = zeroLocus k (Ideal.span (T : Set (MvPolynomial (Fin n) k))))

end MvPolynomial
