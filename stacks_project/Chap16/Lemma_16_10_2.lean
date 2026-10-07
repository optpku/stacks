module

import StacksCheckRecall
public import ReasLib.RingTheory.RegularLocalRing.Parameters.Lifting

@[expose] public section

/- Lemma 16.10.2: for `0 < n` and `0 < e`, regular parameters can be lifted
from a prime localization with prescribed `n`-th-power containment and stable
successive annihilators modulo preceding `e`-th powers. -/
@[stacks 07FD]
#check @PrimeSpectrum.Parameters.Lift.nonempty_of_dimension

#check @PrimeSpectrum.Parameters.Lift
#check @PrimeSpectrum.Parameters.Lift.of
#check @PrimeSpectrum.Parameters.Lift.localized
#check @PrimeSpectrum.Parameters.Lift.spec
#check @PrimeSpectrum.Parameters.Lift.nonempty
#check @RingTheory.Sequence.StableAnnihilators
