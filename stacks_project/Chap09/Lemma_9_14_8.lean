module

public import ReasLib.FieldTheory.SeparableDegree.Embeddings
import StacksCheckRecall

@[expose] public section

/- Lemma 9.14.8 (Tag 09HJ): for a finite extension `K/F`, its separable degree equals the
number of `F`-algebra homomorphisms from `K` into an algebraic closure of `F`. The shared owner
applies to every algebraically closed target. -/
@[stacks 09HJ]
#check Field.sepDegree_eq_natCard_algHom_of_isAlgClosed
