module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.Sheafification
import StacksCheckRecall

@[expose] public section

/- Lemma 7.20.4 (00XM): for a cocontinuous functor of sites, sheafification commutes
with presheaf pullback.  The reusable owner is the canonical comparison of left adjoints;
the concrete weak-sheafification map is exposed as its source-facing invertibility API. -/

@[stacks 00XM "(1)"] #check @CategoryTheory.Functor.CocontinuousPullback.sheafificationCompatibility

@[stacks 00XM "(2)"] #check @CategoryTheory.Functor.CocontinuousPullback.sheafifyMap_isIso
