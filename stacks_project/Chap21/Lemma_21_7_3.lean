module

public import ReasLib.CategoryTheory.Sites.Cohomology.LocallyZero
public import StacksCheckRecall

/-!
Lemma 21.7.3 (01FW) is a recall entry.  For an abelian sheaf `F` on `J`, a class in `F.H' n U`
with `0 < n` is locally zero for `F.cohomologyPresheaf n`.  The predicate-level owner is
`Presheaf.IsLocallyZero`; the cover-shaped declaration is retained as the source-facing view.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace CategoryTheory.Sheaf

@[stacks 01FW "positive cohomology classes are locally zero"]
#check @cohomology_isLocallyZero_of_positive

@[stacks 01FW "positive cohomology classes admit a vanishing cover"]
#check @exists_cover_restrict_eq_zero_of_positive_cohomology_class

end CategoryTheory.Sheaf
