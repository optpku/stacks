/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk.Tensor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 17.16.1 (01CB): the stalk of the tensor product of two module sheaves is canonically
isomorphic to the tensor product of their stalks over the stalk ring. -/
@[stacks 01CB]
#check @RingedSpace.Tensor.Stalk.comparison
#check @RingedSpace.Tensor.Stalk.comparisonInv
#check @RingedSpace.Tensor.Stalk.comparisonIso
#check @RingedSpace.Tensor.Stalk.comparison_hom_inv_id
#check @RingedSpace.Tensor.Stalk.comparison_inv_hom_id
#check @RingedSpace.Tensor.Stalk.comparisonIso_hom
#check @RingedSpace.Tensor.Stalk.comparisonIso_inv

/- The comparison is globally available to typeclass search as an isomorphism. -/
#check @RingedSpace.Tensor.Stalk.comparison_isIso

/- The comparison is natural in both module arguments. -/
#check @RingedSpace.Tensor.Stalk.comparison_naturality
#check @RingedSpace.Tensor.Stalk.comparisonInv_naturality
#check @RingedSpace.Tensor.Stalk.sourceFunctor
#check @RingedSpace.Tensor.Stalk.targetFunctor
#check @RingedSpace.Tensor.Stalk.comparisonNatTrans
#check @RingedSpace.Tensor.Stalk.comparisonInvNatTrans
#check @RingedSpace.Tensor.Stalk.comparisonNatIso
#check @RingedSpace.Tensor.Stalk.comparisonNatIso_inv_app

/- On local pure tensors, the comparison is the pure tensor of the two germs. -/
#check @RingedSpace.Tensor.Stalk.comparison_germ_tensorSectionOver
