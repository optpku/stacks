module

public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Approximation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.168.2

@stack 034Y
-/

/- Lemma 10.168.2 [stacks 034Y]: canonical recall.  The reusable owner
`RingHom.FaithfullyFlat.exists_model` gives the model through the canonical
`Algebra.IsPushout` comparison rather than a chosen tensor-product
equivalence. -/
@[stacks 034Y]
#check @RingHom.FaithfullyFlat.exists_model
