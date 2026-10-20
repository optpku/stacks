module

public import ReasLib.RingTheory.Extension.FirstOrder.Quotient
import StacksCheckRecall

/-!
# The Universal First-Order Quotient Thickening

The canonical map, extension, kernel identification, universal property, and
cotangent comparison are owned by `Ideal.FirstOrder`.

@stack 04ED
-/

@[expose] public section

@[stacks 04ED "canonical quotient map"]
#check @Ideal.FirstOrder.factor

@[stacks 04ED "canonical quotient extension"]
#check @Ideal.FirstOrder.extension

@[stacks 04ED "kernel identification"]
#check @Ideal.FirstOrder.extension_ker

@[stacks 04ED "(1), universal first-order thickening"]
#check @Ideal.FirstOrder.isUniversal

@[stacks 04ED "(2), conormal module"]
#check @Ideal.FirstOrder.cotangentEquiv
