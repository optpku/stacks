module

public import ReasLib.LinearAlgebra.TensorProduct.Bimodule.Associator
import StacksCheckRecall

open scoped TensorProduct.Bimodule

@[expose] public section

/-!
# Mixed-base tensor associativity

@stack 00D2

Lemma 10.12.7 is a source-facing recall of the reusable mixed-base associator.  The additive
equivalence is the root owner; its `A`- and `B`-linear views share the same underlying map.
-/

/- Transported left-factor action. -/
#check @TensorProduct.Bimodule.leftModule

/- Transported right-factor action. -/
#check @TensorProduct.Bimodule.rightModule

/- Base/right scalar commutation. -/
#check @TensorProduct.Bimodule.Right.smulCommClassBase

/- The shared additive root of the two linear views. -/
#check @TensorProduct.Bimodule.assoc

/- Pure-tensor formula. -/
#check @TensorProduct.Bimodule.assoc_tmul

/- Inverse pure-tensor formula. -/
#check @TensorProduct.Bimodule.assoc_symm_tmul

/- Lemma 10.12.7 (Tag 00D2): the canonical `A`-linear mixed-base associator. -/
@[stacks 00D2 "A-linear associator"]
#check @TensorProduct.Bimodule.assocLeft

/- The symmetric `B`-linear view. -/
#check @TensorProduct.Bimodule.assocRight

/- The two views share the same underlying map. -/
#check @TensorProduct.Bimodule.assocLeft_apply
#check @TensorProduct.Bimodule.assocRight_apply
#check @TensorProduct.Bimodule.assocLeft_symm_apply
#check @TensorProduct.Bimodule.assocRight_symm_apply

end
