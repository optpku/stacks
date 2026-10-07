module

public import ReasLib.Algebra.Category.CommAlgCat.FilteredColimit.Etale
import StacksCheckRecall

/-!
@stack 07RI
-/

@[expose] public section

/- Lemma 10.168.7 [stacks 07RI]: canonical recall.  The reusable owner is
`CommAlgCat.FilteredColimit.Etale.exists_stage`, stated for an arbitrary
filtered diagram of commutative algebras. -/
@[stacks 07RI]
#check @CommAlgCat.FilteredColimit.Etale.exists_stage
