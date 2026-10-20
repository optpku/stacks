module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Derived.ChainMap
import StacksCheckRecall

/-!
Lemma 21.53.2 (09BD): a derived morphism from the constant sheaf on a bounded complex of finite
projective modules is locally represented by chain maps. ReasLib separates representation on one
slice from the cover-wise predicate.
-/

@[expose] public section

open CategoryTheory

@[stacks 09BD]
#check @CategoryTheory.Sheaf.DerivedRestriction.locallyRepresentedAt_terminal_of_isBoundedFiniteProjective

#check @CategoryTheory.Sheaf.DerivedRestriction.IsRepresentedOn
#check @CategoryTheory.Sheaf.DerivedRestriction.IsLocallyRepresentedAt
#check @CategoryTheory.Sheaf.DerivedRestriction.locallyRepresentedAt_of_isBoundedFiniteProjective
#check @CategoryTheory.Sheaf.DerivedRestriction.isRepresentedOn_iff
#check @CategoryTheory.Sheaf.DerivedRestriction.isLocallyRepresentedAt_iff

end
