module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.IndSmooth.SquareZero.Quotient

@[expose] public section

/- Lemma 16.5.1 (tag 07CK): the square-zero smooth-quotient factorization is
owned by ReasLib. -/

@[stacks 07CK]
#check @AlgHom.QuotientFactorisation.Smooth.nonempty_of_squareZero

#check @AlgHom.QuotientFactorisation.Smooth
#check @AlgHom.QuotientFactorisation.Smooth.of
#check @AlgHom.QuotientFactorisation.Smooth.spec
