module

public import ReasLib.CategoryTheory.Monoidal.Adjunction.SupportedTensor
import StacksCheckRecall

@[expose] public section

/-!
# Tensor products with derived closed support

The closed-subset construction is the specialization of the generic two-adjunction API below.
When the derived tensor is represented by explicit bifunctors, `SupportTensor.of` is the pointwise
owner and `supportTensorOfFunctors` is its family bridge; `SupportTensor.ofMonoidal` is the monoidal
pointwise specialization, while `supportTensorOf` and `supportTensor` retain convenient family and
projection-formula forms.  All owners live in ReasLib and have no chapter dependency.
-/

open CategoryTheory

noncomputable section

/- Remark 20.34.9: the supported tensor map is the mate of an ambient tensor map under the
support adjunction.  The explicit-map owner preserves the weak source assumptions; the canonical
projection-formula owner is a specialization. -/
@[stacks 0G75 "Remark 20.34.9 tensor product with support"]
#check @CategoryTheory.Adjunction.supportTensorOfFunctors

#check @CategoryTheory.Adjunction.SupportTensor.of
#check @CategoryTheory.Adjunction.SupportTensor.of_spec
#check @CategoryTheory.Adjunction.SupportTensor.of_comp_counit
#check @CategoryTheory.Adjunction.SupportTensor.ofMonoidal
#check @CategoryTheory.Adjunction.SupportTensor.ofMonoidal_spec
#check @CategoryTheory.Adjunction.SupportTensor.ofMonoidal_comp_counit

#check @CategoryTheory.Adjunction.supportTensorOf
#check @CategoryTheory.Adjunction.supportTensorOfFunctors_spec
#check @CategoryTheory.Adjunction.supportTensorOfFunctors_commSq
#check @CategoryTheory.Adjunction.supportTensorOfFunctors_comp_counit
#check @CategoryTheory.Adjunction.supportTensorOfFunctors.natTrans
#check @CategoryTheory.Adjunction.supportTensorOfFunctors.natTrans_app

#check @CategoryTheory.Adjunction.supportTensorOf_spec
#check @CategoryTheory.Adjunction.supportTensorOf_commSq
#check @CategoryTheory.Adjunction.supportTensorOf_comp_counit
#check @CategoryTheory.Adjunction.supportTensor
#check @CategoryTheory.Adjunction.supportTensorPush
#check @CategoryTheory.Adjunction.supportTensorNatTrans
#check @CategoryTheory.Adjunction.supportTensorPushNatTrans
#check @CategoryTheory.Adjunction.supportTensor_commSq
#check @CategoryTheory.Adjunction.supportTensor_comp_counit

end
