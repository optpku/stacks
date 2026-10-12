/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Principal

/-!
# Principal derived completion comparison

The canonical ReasLib owner compares objectwise derived limits of the two-term and
principal-quotient tensor towers. Its stage compatibility condition records that the natural
transformation is induced by the explicit tower augmentation.

@stack 0923
-/

@[expose] public section

/- Lemma 15.94.2: the natural comparison from principal derived completion to naive principal
completion is an isomorphism exactly when the `f`-power torsion of the ring is bounded. -/
@[stacks 0923 "Lemma 15.94.2"]
#check @CategoryTheory.DerivedCategory.PrincipalPower.completionComparison_isIso_iff

/- The source, target, and stagewise comparison are concrete ReasLib data owners. -/
#check @CategoryTheory.DerivedCategory.PrincipalPower.twoTermTensorSystem
#check @CategoryTheory.DerivedCategory.PrincipalPower.cokernelTensorSystem
#check @CategoryTheory.DerivedCategory.PrincipalPower.tensorAugmentationSystem
