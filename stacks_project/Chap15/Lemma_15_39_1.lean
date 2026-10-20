module

public import ReasLib.RingTheory.Smooth.Adic.PowerSeries
import StacksCheckRecall

/-!
# Lemma 15.39.1

@stack 07NL
-/

@[expose] public section

/- Lemma 15.39.1 (1), tag `07NL`: a characteristic-zero field's finite-variable power series
ring is maximal-ideal-adically formally smooth over `ℚ`. -/
@[stacks 07NL "part 1"]
#check @rational_to_mvPowerSeries_formally_smooth_for_madic

/- Lemma 15.39.1 (2), tag `07NL`: a characteristic-`p` field's finite-variable power series
ring is maximal-ideal-adically formally smooth over `ZMod p`. -/
@[stacks 07NL "part 2"]
#check @zmod_to_mvPowerSeries_formally_smooth_for_madic

/- Lemma 15.39.1 (3), tag `07NL`: a Cohen ring's finite-variable power series ring is
maximal-ideal-adically formally smooth over `ℤ`. -/
@[stacks 07NL "part 3"]
#check @int_to_mvPowerSeries_over_cohenRing_formally_smooth_for_madic
