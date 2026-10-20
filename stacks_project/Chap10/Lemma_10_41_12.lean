module

public import ReasLib.RingTheory.Module.Support.Flat
import StacksCheckRecall

/-!
# Generalizations in the support of a flat module

@stack 080T
-/

@[expose] public section

/- Lemma 10.41.12: if `N` is a finite `S`-module that is flat over `R`, then
generalizations lift along the map `support S N → Spec R` induced by
`PrimeSpectrum.comap (algebraMap R S)`. -/
@[stacks 080T]
#check @Module.generalizingMap_support_comap_of_flat
