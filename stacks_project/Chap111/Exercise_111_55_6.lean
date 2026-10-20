module

public import ReasLib.RingTheory.MvPolynomial.SquareMonomials
import StacksCheckRecall

@[expose] public section

/- Exercise 111.55.6. -/
@[stacks 07DK]
#check
  (MvPolynomial.squareMonomialsIdeal_not_spanRank_le_two :
    ¬ (MvPolynomial.squareMonomialsIdeal ℂ).spanRank ≤ 2)
