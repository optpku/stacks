module

public import ReasLib.CategoryTheory.Sites.Sheaf.Yoneda

import StacksCheckRecall

@[expose] public section

/-!
[stacks 00Z8]

Definition 7.47.10 recalls `Presheaf.IsSheaf`; the coverwise Yoneda formulation is its reusable
characterization.
-/

@[stacks 00Z8] #check CategoryTheory.Presheaf.IsSheaf
#check CategoryTheory.Presheaf.isSheaf_iff_forall_yonedaSheafCondition
