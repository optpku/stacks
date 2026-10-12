/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.TwoFibreProduct.Stackification
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.TwoFibreProduct
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Local equivalences are preserved by the groupoid two-fibre-product map. -/
#check @FiberedCategoryOver.Groupoids.TwoFibreProduct.map.isLocalEquivalence

/- This local-equivalence result is the reusable intermediate criterion. -/
#check @FiberedCategoryOver.Groupoids.TwoFibreProduct.map.isStackification_of_isLocalEquivalence

/- Lemma 8.9.3 (04Y2): the stackification of a two-fibre product of categories fibred in
groupoids is the two-fibre product of their stackifications. -/
@[stacks 04Y2 "two-fibre-products preserve stackifications"]
#check @FiberedCategoryOver.Groupoids.TwoFibreProduct.map.exists_of_stackifications

/- The heterogeneous theorem remains available when the six total categories live in independent
universes; the direct groupoid criterion handles already-compatible target legs. -/
#check @BasedCategory.PseudoPullback.cartesianMap.exists_of_stackifications
#check @BasedCategory.PseudoPullback.cartesianMap.isStackification
#check @FiberedCategoryOver.Groupoids.TwoFibreProduct.map.isStackification

end CategoryTheory
