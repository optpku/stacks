module

public import ReasLib.RingTheory.RingHom.IndEtale.Composition
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.154.5, tag `08HS`, is recalled through the canonical source-facing
comparison theorem and its arbitrary-presentation companion in the shared
ind-etale ring-map API.

@stack 08HS
-/

/- Lemma 10.154.5, tag `08HS`: the canonical common-base comparison is ind-etale. -/
@[stacks 08HS]
#check @RingHom.IndEtale.of_comp

@[stacks 08HS "common-base comparison"]
#check @RingHom.IndEtale.Raw.of_over_common_base
