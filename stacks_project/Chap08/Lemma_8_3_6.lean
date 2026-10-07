module

public import ReasLib.CategoryTheory.Sites.Descent.Family.Canonical
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 8.3.6

The overlap formula is a statement about the canonical descent datum.  ReasLib records both its
arbitrary chosen-pullback owner and the literal chosen-presentation morphism used in the source.
-/

namespace CategoryTheory

#check @DescentDatum.Canonical.overlapIso

@[stacks 026D "chosen-presentation overlap comparison"]
#check @DescentDatum.Canonical.presentationHom

#check @DescentDatum.Canonical.chosenOverlapIso

end CategoryTheory
