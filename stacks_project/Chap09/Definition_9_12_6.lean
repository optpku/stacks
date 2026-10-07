module

public import ReasLib.FieldTheory.Polynomial.SeparableDegree
import StacksCheckRecall

@[expose] public section

/- Definition 9.12.6 (Tag 09H5): the textbook separable degree is the canonical
`Polynomial.natSepDegree`; over an algebraically closed extension it counts distinct roots. -/
@[stacks 09H5]
#check Polynomial.natSepDegree
#check Polynomial.natSepDegree_eq_card_rootSet
