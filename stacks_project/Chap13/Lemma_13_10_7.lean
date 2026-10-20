module

import ReasLib.Algebra.Homology.HomotopyCategory.DegreewiseSplit.NormalForm
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.10.7

Endpoint-normalized degreewise-split models of distinguished triangles are
owned by the neutral homotopy-category API.
-/

/- Lemma 13.10.7 (Stacks 0G6C): every distinguished triangle of cochain
complexes is isomorphic, through the identity on its first and third objects,
to the triangle of a degreewise split short complex. -/
@[stacks 0G6C] #check
  @CategoryTheory.HomotopyCategory.DegreewiseSplitModel.nonempty_of_distinguished
