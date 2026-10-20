module

public import ReasLib.RingTheory.Algebra.TensorProduct.BaseChange
import StacksCheckRecall

/-!
# Tensor base-change support for Lemma 10.48.2

The separable-closure tensor comparison used in the source proof is an instance of the generic
right-oriented base-change equivalence. This compatibility file recalls that owner instead of
rebuilding its noncanonical tensor-product algebra instances.

@stack 037S
-/

@[expose] public section

@[stacks 037S "separable-closure tensor base-change comparison"]
#check @Algebra.TensorProduct.baseChangeRight
