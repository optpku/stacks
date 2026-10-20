module

public import ReasLib.RingTheory.Completion.RegularPresentation
import StacksCheckRecall

/-!
# Lemma 15.38.4

@stack 0C35
-/

@[expose] public section

/- Lemma 15.38.4, tag `0C35`: a complete regular local `k`-algebra with separable residue
field is a finite-variable formal power-series algebra over that residue field. -/
@[stacks 0C35]
#check @exists_algEquiv_mvPowerSeries_residueField_of_isSeparableOver_of_isRegularLocalRing
