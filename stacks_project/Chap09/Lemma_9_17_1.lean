module

public import ReasLib.Algebra.Group.Torsion
import StacksCheckRecall

@[expose] public section

/- Lemma 9.17.1 (Tag 09HX): an abelian group whose exponent divides `n` and whose `d`-torsion
subgroup has cardinality `d` for every divisor `d` of `n` is cyclic. The canonical mathlib theorem
`isAddCyclic_of_card_nsmul_eq_zero_le` is stronger once finiteness is available; the project API
derives that finiteness from the source-shaped divisor condition. -/
#check AddCommGroup.finiteOfTorsionCardinalLe
#check AddCommGroup.isAddCyclicOfTorsionCardinalLe
#check AddCommGroup.natCardDvdOfTorsionCardinalLe
@[stacks 09HX]
#check AddCommGroup.isAddCyclicOfTorsionCardinalEq
#check isAddCyclic_of_card_nsmul_eq_zero_le
