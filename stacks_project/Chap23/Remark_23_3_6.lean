module

public import ReasLib.RingTheory.DividedPowers.Category.Forget
import StacksCheckRecall

@[expose] public section

/- Remark 23.3.6 (tag `07GY`): the forgetful functor from divided power rings to commutative
rings does not preserve all colimits. -/
open CategoryTheory CategoryTheory.Limits

@[stacks 07GY]
#check (DividedPowerRing.forgetCommRing.notPreservesColimits :
  ¬ PreservesColimits DividedPowerRing.forgetCommRing)

#check @DividedPowerRing.forgetCommRing.notPreservesPushouts
