module

public import ReasLib.RingTheory.RingHom.IndEtale.Colimit
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.154.3, tag `0BSJ`, is the shared filtered-colimit closure theorem
for ind-etale ring maps.

@stack 0BSJ
-/

@[stacks 0BSJ]
#check @RingHom.IndEtale.Raw.under_presentation

@[stacks 0BSJ "filtered-colimit closure"]
#check @RingHom.IndEtale.Raw.of_isColimit

@[stacks 0BSJ "filtered-colimit algebra map"]
#check @RingHom.IndEtale.Raw.algebraMap_of_isColimit
