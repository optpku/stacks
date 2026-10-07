module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
import StacksCheckRecall

/-!
# Lemma 18.28.12

The tensor product of flat module sheaves is flat.  This is the ringed-site specialization of the
general closure of monoidal flat objects under tensor product.
-/

@[expose] public section

/- Lemma 18.28.12 (0G6Q): monoidal flat objects are closed under tensor product. -/
@[stacks 0G6Q]
#check @CategoryTheory.MonoidalCategory.isFlat_tensor
