module

public import ReasLib.RingTheory.CohenMacaulay.TensorProduct.FieldExtension
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.167.1

@stack 045M
-/

/- Lemma 10.167.1 (Stacks tag `045M`): the symmetric finite-type tensor
product criterion is owned by the shared Cohen--Macaulay API. -/
@[stacks 045M]
#check @CohenMacaulayRing.tensorProduct_of_essFiniteType

@[stacks 045M "left finite-type tensor criterion"]
#check @CohenMacaulayRing.tensorProduct_of_essFiniteType_left

@[stacks 045M "right finite-type tensor criterion"]
#check @CohenMacaulayRing.tensorProduct_of_essFiniteType_right
