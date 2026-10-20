module

public import ReasLib.RingTheory.Ideal.MinimalPrime.Injective
import StacksCheckRecall

@[expose] public section

universe u

/- Example 47.3.6: if `R` is reduced and `p` is a minimal prime of `R`, then the
field `Localization.AtPrime p.1` is injective as an `R`-module. -/
@[stacks 08XT] #check
  (minimalPrimes.injective_localizationAtPrime :
    ∀ {R : Type u} [CommRing R] [IsReduced R] (p : minimalPrimes R),
      Module.Injective R (Localization.AtPrime p.1))
