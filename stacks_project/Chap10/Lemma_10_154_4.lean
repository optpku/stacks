module

public import ReasLib.RingTheory.RingHom.IndEtale.Colimit
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.154.4, tag `0GIM`, is the directed-arrow-colimit form of the
shared ind-etale closure API.

@stack 0GIM
-/

@[stacks 0GIM]
#check @RingHom.IndEtale.Raw.colimit_of_directed
