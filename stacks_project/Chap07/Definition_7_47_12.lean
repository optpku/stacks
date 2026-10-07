module

public import Mathlib.CategoryTheory.Sites.Canonical

import StacksCheckRecall

@[expose] public section

/- Definition 7.47.12: the finest topology on a category such that all representable
presheaves are sheaves is the canonical topology. -/
@[stacks 00ZA] #check @CategoryTheory.Sheaf.canonicalTopology

#check CategoryTheory.Sheaf.isSheaf_yoneda_obj
