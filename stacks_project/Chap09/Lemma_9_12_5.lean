module

public import ReasLib.FieldTheory.Polynomial.SeparableDegree
import StacksCheckRecall

@[expose] public section

/- Lemma 9.12.5 (Tag 09H4): over an algebraically closed extension of a characteristic-`p`
field, `P` and `P.comp (X ^ p)` have equally many distinct roots. -/
@[stacks 09H4]
#check Polynomial.card_rootSet_comp_X_pow_eq
