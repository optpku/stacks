module

public import ReasLib.FieldTheory.IntermediateField.Algebraic
import StacksCheckRecall

@[expose] public section

/- Lemma 9.8.10 (Tag 0BID): a subring of an algebraic field extension that contains the base
field is a field. -/
@[stacks 0BID]
#check Subring.isFieldOfAlgebraic
