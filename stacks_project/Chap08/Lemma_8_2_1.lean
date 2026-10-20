module

public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.2.1: the assignment sending `V/U : Over U` to the morphism type
`Hom(V^* x, V^* y)` is the canonical Hom-presheaf. -/
@[stacks 026A "canonical Hom-presheaf of a fiber pseudofunctor"]
#check @Pseudofunctor.presheafHom

end CategoryTheory
