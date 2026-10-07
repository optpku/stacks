module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.66.17
@stack 05CB

The source-facing injectivity statement is owned by the canonical
weak-associated-prime localization namespace; this chapter file records it.
-/

@[stacks 05CB "Lemma 10.66.17"]
#check @weaklyAssociatedPrimes.Localization.localizationMap_injective
