/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.Augmented
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

namespace CategoryTheory

/- Lemma 25.4.3 is recalled from the neutral simplicial-presheaf homology comparison API. -/
@[stacks 01GD] #check
  @SimplicialPresheaf.Homology.Comparison.ofCoskUnit
#check @SimplicialPresheaf.Homology.Comparison.ofCoskeletal

end CategoryTheory
