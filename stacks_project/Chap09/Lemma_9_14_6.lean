module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 9.14.6: for an algebraic field extension `E / F`, the unique subextension `E / E_{sep} / F`
with `E_{sep} / F` separable and `E / E_{sep}` purely inseparable is the canonical intermediate
field `separableClosure F E`; equivalently, an intermediate field `L` has these two properties
exactly when `L = separableClosure F E`. This is the canonical theorem
`eq_separableClosure_iff`. -/
@[stacks 030K]
#check eq_separableClosure_iff
