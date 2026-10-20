module

public import ReasLib.RingTheory.Regular.Field
import StacksCheckRecall

/-!
Lemma 15.41.6 (07EQ): a field extension is a regular ring map exactly when it is separable
in the Stacks Project sense. The reusable owner is `RingHom.Regular.algebraMap_iff_isSeparableOver`.
@stack 07EQ
-/

@[expose] public section

/- Lemma 15.41.6: a field extension is a regular ring map if and only if it is
separable in the Stacks Project sense. -/
@[stacks 07EQ] #check @RingHom.Regular.algebraMap_iff_isSeparableOver
