module

public import ReasLib.RingTheory.CohenMacaulay.Module.Self
import StacksCheckRecall

@[expose] public section

/-!
# Localization of a Cohen-Macaulay local ring

@stack 00NB
-/

/- Lemma 10.104.5: localization at a prime preserves Cohen-Macaulayness of a Noetherian local
ring. -/
@[stacks 00NB]
#check @Module.CohenMacaulay.localizationAtPrime_self
