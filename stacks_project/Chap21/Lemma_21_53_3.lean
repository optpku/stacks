/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Derived.Morphism
import StacksCheckRecall

/-!
Lemma 21.53.3 (09BE): over a terminal object, a morphism between constant derived sheaves with
perfect source is locally induced by morphisms in the coefficient derived category.
-/

@[expose] public section

open CategoryTheory

@[stacks 09BE]
#check @CategoryTheory.Sheaf.DerivedRestriction.locallyInducedAt_of_isPerfect

#check @CategoryTheory.Sheaf.constantSheafOverIso
#check @CategoryTheory.Sheaf.constantSheafOverDerivedIso
#check @CategoryTheory.Sheaf.DerivedRestriction.IsInducedOn
#check @CategoryTheory.Sheaf.DerivedRestriction.IsLocallyInducedAt
#check @CategoryTheory.Sheaf.DerivedRestriction.isInducedOn_iff
#check @CategoryTheory.Sheaf.DerivedRestriction.isLocallyInducedAt_iff

end
