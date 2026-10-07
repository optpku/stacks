module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.WeaklyUnramifiedBaseChange
import StacksCheckRecall

@[expose] public section

/-!
@stack 09ER
# Lemma 15.116.3

The finite-separable totally ramified base-change consequences are owned by ReasLib.  The raw
tensor field theorem and the normalized integral-closure/DVR bridge remain separately named, so
later statements can use only the piece they need.
-/

open DVR.Field
open IsExtensionOfDiscreteValuationRings

/- Lemma 15.116.3 (1): the fraction-field tensor product is a field. -/
@[stacks 09ER "Lemma 15.116.3 (1): tensor product is a field"]
#check @DVR.BaseChange.tensorField_of_weaklyUnramified_of_totallyRamified

/- Lemma 15.116.3 (2): the source integral closure is a DVR. -/
@[stacks 09ER "Lemma 15.116.3 (2): source normalization is a DVR"]
#check @DVR.BaseChange.integralClosure_isDVR_of_totallyRamified

/- Lemma 15.116.3 (3): the target normalized integral closure is a DVR. -/
@[stacks 09ER "Lemma 15.116.3 (3): target normalization is a DVR"]
#check @DVR.BaseChange.target_isDomain_of_weaklyUnramified_of_totallyRamified
#check @DVR.BaseChange.target_isDVR_of_weaklyUnramified_of_totallyRamified

/- Lemma 15.116.3 (4): the normalized map is exposed as a weak solution. -/
@[stacks 09ER "Lemma 15.116.3 (4): normalized map is weakly unramified"]
#check @DVR.BaseChange.weakSolution_of_weaklyUnramified_of_totallyRamified

/- Reusable two-step tower owner for later ramification-elimination statements. -/
#check @DVR.BaseChange.WeaklyUnramifiedTower
#check @DVR.BaseChange.WeaklyUnramifiedTower.spec
