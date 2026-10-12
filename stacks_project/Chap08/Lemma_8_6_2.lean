/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.CategoryOfElements
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 8.6.2

The chapter entry recalls both the objectwise category-of-elements/sheaf criterion and its
functorial restriction to an equivalence between set-valued sheaves and stacks in sets.  The
explicit coverwise descent construction is proof infrastructure and is intentionally not exported
from the chapter-facing module.
-/

namespace CategoryTheory

/- Lemma 8.6.2 (0430): a set-valued presheaf is a `J`-sheaf exactly when its opposite
category-of-elements projection is a stack in sets. -/
@[stacks 0430]
#check @CategoryOfElements.isSheaf_iff_stackInSets

#check @CategoryOfElements.isSheaf_iff_stackOnSite
#check @IsStack.InSets.iff_isStackOnSite
#check @StackOver.Sets.ofSheaf
#check @StackOver.Sets.ofSheaf.obj.toSets
#check @StackOver.Sets.ofSheaf.obj.p
#check @StackOver.Sets.ofSheaf.map.toFunctor
#check @StackOver.Sets.sheafEquivalence
#check @StackOver.Sets.sheafEquivalence.toStack
#check @StackOver.Sets.sheafEquivalence.toSheaf
#check @StackOver.Sets.sheafEquivalence.toStack_eq_ofSheaf
#check @StackOver.Sets.SheafEquivalence.directEquivalence.functor.obj
#check @StackOver.Sets.sheafEquivalence.toStack.obj.p
#check @StackOver.Sets.sheafEquivalence.toStack.map.toFunctor
#check @StackOver.Sets.sheafEquivalence.toSheaf.obj.presheaf

end CategoryTheory
