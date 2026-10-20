/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.TwoFibreProduct.Isomorphism.Collapse
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.2.5 (1): the source two-fibre product
`S ×_{S ×_C S, (x, y)} C/U` is fibred in setoids over `C/U`. -/
@[stacks 04SI "(1)"]
#check @FiberedCategoryOver.TwoFibreProduct.Isomorphism.sourceProjectionInSetoids
#check @FiberedCategoryOver.TwoFibreProduct.Isomorphism.sourceSetoids
#check @FiberedCategoryOver.TwoFibreProduct.Isomorphism.sourceSetoids.p

/- Lemma 8.2.5 (2): after normalizing presheaf values with `ULift`, the isomorphism presheaf is
identified with the fiberwise isomorphism-class presheaf of the literal two-fibre-product source. -/
@[stacks 04SI "(2)"]
#check @FiberedCategoryOver.TwoFibreProduct.Isomorphism.collapse.sourcePresheafIso
#check @FiberedCategoryOver.TwoFibreProduct.Isomorphism.collapse.sourcePresheafIso.hom.app
#check @FiberedCategoryOver.TwoFibreProduct.Isomorphism.collapse.sourcePresheafIso.inv.app_mk_ulift

end CategoryTheory
