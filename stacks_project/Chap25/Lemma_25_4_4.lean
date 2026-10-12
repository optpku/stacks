/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.Augmented.Homology
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

namespace CategoryTheory

/- Lemma 25.4.4 (1): a local hypercover has vanishing positive-degree homology sheaves. -/
@[stacks 01GE "positive degrees"] #check
  @SimplicialObject.Augmented.IsLocalHypercover.Homology.succ_isZero

/- Lemma 25.4.4 (2): its degree-zero homology is the free abelian sheaf on the augmentation
target. -/
@[stacks 01GE "degree zero"] #check
  @SimplicialObject.Augmented.IsLocalHypercover.Homology.augmentationMap_isIso

end CategoryTheory
