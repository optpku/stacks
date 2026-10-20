module

public import ReasLib.FieldTheory.Frobenius.Polynomial
import StacksCheckRecall

@[expose] public section

/- Lemma 9.12.1 (Tag 09H0): the derivative criterion is owned by
`Polynomial.separable_iff_derivative_ne_zero`; in the zero-derivative case the shared
Frobenius API supplies an irreducible separable contraction. -/
@[stacks 09H0]
#check Polynomial.separable_iff_derivative_ne_zero
#check Irreducible.hasSeparableContraction
#check Polynomial.existsIrreducibleSeparableExpandOfDerivativeEqZero
