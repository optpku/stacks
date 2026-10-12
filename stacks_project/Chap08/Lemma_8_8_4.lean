/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.TwoFibreProduct
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.8.4: the two-fibre product of three chosen stackifications is a stackification of the
original two-fibre product. The source-facing existence theorem is heterogeneous in all six
total-category universes. -/
@[stacks 04Y1 "two-fibre-products preserve stackifications"]
#check @BasedCategory.PseudoPullback.cartesianMap.exists_of_stackifications

#check @CartesianCospanTransform
#check @CartesianCospanTransform.ofPrecompLifts
#check @CartesianCospanTransform.ofPrecompLifts.left
#check @CartesianCospanTransform.ofPrecompLifts.right
#check @CartesianCospanTransform.ofPrecompLifts.base
#check @CartesianCospanTransform.ofPrecompLifts.leftIso
#check @CartesianCospanTransform.ofPrecompLifts.rightIso
#check @FiberedCategoryOver.CospanTransform.toCartesian
#check @FiberedCategoryOver.CospanTransform.toCartesian.left
#check @FiberedCategoryOver.CospanTransform.toCartesian.right
#check @FiberedCategoryOver.CospanTransform.toCartesian.base
#check @FiberedCategoryOver.TwoFibreProduct.map.toCartesianBasedFunctor
#check @BasedCategory.PseudoPullback.cartesianMap
#check @BasedCategory.PseudoPullback.cartesianMap.isLocalEquivalence
#check @BasedCategory.PseudoPullback.cartesianMap.isStackification_of_isLocalEquivalence
#check @BasedCategory.PseudoPullback.cartesianMap.isStackification
#check @BasedCategory.PseudoPullback.cartesianMap.isStackification_ofPrecompLifts

/- The reusable closure theorem separates the local-equivalence input from the stackification
specialization used by the source statement. -/
#check @FiberedCategoryOver.TwoFibreProduct.map.isStackification
#check @FiberedCategoryOver.TwoFibreProduct.map.isStackification_of_isLocalEquivalence
#check @FiberedCategoryOver.TwoFibreProduct.map.exists_of_stackifications

end CategoryTheory
