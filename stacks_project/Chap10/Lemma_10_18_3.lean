module

public import ReasLib.RingTheory.LocalRing.Characterization
import StacksCheckRecall

/-!
# Characterizations of local rings

@stack 00E9

Lemma 10.18.3 identifies local rings through their closed points, maximal
ideals, and units.
-/

@[expose] public section

@[stacks 00E9 "source four-clause form"]
#check @IsLocalRing.tfae

@[stacks 00E9 "closed-point criterion"]
#check @PrimeSpectrum.isClosed_singleton_iff_isMaximal

@[stacks 00E9 "unit criterion"]
#check @IsLocalRing.isUnit_or_isUnit_one_sub_self

@[stacks 00E9 "local-ring constructor"]
#check @IsLocalRing.of_isUnit_or_isUnit_one_sub_self
