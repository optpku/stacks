module

public import ReasLib.RingTheory.KrullDimension.Integral
import StacksCheckRecall

/-!
# Krull Dimension and Closed Points Under Integral Maps

This entry recalls the integral-extension Krull-dimension owner in ReasLib.

@stack 00OJ
-/

@[expose] public section

/- Lemma 10.112.3 (1) (Stacks tag `00OJ`): an integral ring map does not
increase Krull dimension. -/
@[stacks 00OJ "(1)"]
#check @RingHom.IsIntegral.ringKrullDim_le

/- The algebra-map companion to clause (1). -/
#check @ringKrullDim_le_of_isIntegral

/- Lemma 10.112.3 (2) (Stacks tag `00OJ`): an integral ring map sends closed
points of the source spectrum to closed points of the target spectrum. -/
@[stacks 00OJ "(2)"]
#check @PrimeSpectrum.isClosed_comap_singleton_of_isIntegral
