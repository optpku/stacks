module

public import Mathlib.CategoryTheory.Sites.Sheaf
import StacksCheckRecall

@[expose] public section

/-!
Lemma 21.8.2 (03AN) is a direct recall of the canonical multiequalizer formulation of the
sheaf condition.  The generic library theorem is retained: it applies to any target category
with the required multiequalizers, and specializes to abelian presheaves by taking
`A := AddCommGrpCat`.
-/

open CategoryTheory

/- Lemma 21.8.2 (03AN): for every covering family, the canonical map from `F.obj (op U)` to the
   associated multiequalizer is an isomorphism exactly when `F` is a sheaf. -/
@[stacks 03AN "sheaf condition via the canonical multiequalizer"]
#check @Presheaf.isSheaf_iff_multiequalizer

@[stacks 03AN "canonical map to the covering multiequalizer"]
#check @GrothendieckTopology.Cover.toMultiequalizer

end
