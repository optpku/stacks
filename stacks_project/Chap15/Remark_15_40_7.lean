module

public import ReasLib.RingTheory.Completion.BaseChange
import StacksCheckRecall

/-!
# Remark 15.40.7 (07NS)

@stack 07NS
-/

@[expose] public section

/- The concrete completed base-change ring and its canonical map to a complete local target. -/
#check @AdicCompletion.BaseChange.ideal
#check @AdicCompletion.BaseChange.ring
#check @AdicCompletion.BaseChange.map
#check @AdicCompletion.BaseChange.map_comp_algebraMap

/- Remark 15.40.7 (1) (07NS): existence of the formally smooth lift and surjectivity of its
completed base-change map. -/
@[stacks 07NS "Remark 15.40.7 (1)"]
#check @AdicCompletion.BaseChange.existsFormallySmoothLift

/- Remark 15.40.7 (2) (07NS): a surjective base map makes the lifted map surjective. -/
@[stacks 07NS "Remark 15.40.7 (2)"]
#check @AdicCompletion.BaseChange.toTargetSurjectiveOfBaseSurjective

/- Remark 15.40.7 (3) (07NS): a finite base map makes the target finite over the lift. -/
@[stacks 07NS "Remark 15.40.7 (3)"]
#check @AdicCompletion.BaseChange.targetFiniteOfBaseFinite

/- Remark 15.40.7 (4) (07NS): flatness makes the canonical completed base-change map
bijective.  Keeping the result on the explicit map avoids selecting inverse data from a deferred
proof. -/
@[stacks 07NS "Remark 15.40.7 (4)"]
#check @AdicCompletion.BaseChange.mapBijectiveOfFlat
