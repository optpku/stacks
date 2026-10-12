/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.LowerShriek.Derived
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace CategoryTheory.FiberedCategoryOver

/- Lemma 21.38.5 (08PC) (1): the module and abelian inverse-image functors attached to a
fibered-category morphism admit the canonical lower-shriek left adjoints. -/
@[stacks 08PC "(1) module inverse image admits lower shriek"]
#check @moduleInverseImage.isRightAdjoint

@[stacks 08PC "(1) abelian inverse image admits lower shriek"]
#check @abelianInverseImage.isRightAdjoint

@[stacks 08PC "(1) module lower shriek"]
#check @moduleLowerShriek

@[stacks 08PC "(1) abelian lower shriek"]
#check @abelianLowerShriek

/- Lemma 21.38.5 (08PC) (2): the canonical mate identifies ordinary module lower shriek
after forgetting module structure with ordinary abelian lower shriek. -/
@[stacks 08PC "(2) ordinary forgetful comparison"]
#check @lowerShriekForgetComparison

@[stacks 08PC "(2) ordinary forgetful comparison isomorphism"]
#check @moduleInverseImageUnderlyingIso

@[stacks 08PC "(2) ordinary forgetful comparison is invertible"]
#check @lowerShriekForgetComparison_isIso

namespace DerivedLowerShriek

/- Lemma 21.38.5 (08PC) (3): the exact derived inverse-image functors admit the canonical
derived lower-shriek left adjoints. -/
@[stacks 08PC "(3) derived module inverse image"]
#check @moduleInverseImage

@[stacks 08PC "(3) derived abelian inverse image"]
#check @abelianInverseImage

@[stacks 08PC "(3) derived module lower shriek"]
#check @moduleLowerShriek

@[stacks 08PC "(3) derived abelian lower shriek"]
#check @abelianLowerShriek

@[stacks 08PC "(3) derived module adjunction"]
#check @moduleAdjunction

@[stacks 08PC "(3) derived abelian adjunction"]
#check @abelianAdjunction

/- Lemma 21.38.5 (08PC) (4): the canonical derived mate identifies derived module lower
shriek after forgetting module structure with derived abelian lower shriek. -/
@[stacks 08PC "(4) derived forgetful square"]
#check @underlyingIso

@[stacks 08PC "(4) derived forgetful comparison"]
#check @underlyingComparison

@[stacks 08PC "(4) derived forgetful comparison is invertible"]
#check @underlyingComparison_isIso

end DerivedLowerShriek

end CategoryTheory.FiberedCategoryOver
