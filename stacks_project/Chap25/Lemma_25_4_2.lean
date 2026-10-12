/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Map
public import ReasLib.CategoryTheory.Sites.Simplicial.Augmented
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

namespace CategoryTheory

/- Lemma 25.4.2 [stacks 01GC], positive-degree clause. -/
@[stacks 01GC "positive degrees"] #check
  @SimplicialPresheaf.Homology.CechNerve.succ_isZero

/- Lemma 25.4.2 [stacks 01GC], degree-zero augmentation clause. -/
@[stacks 01GC "degree zero"] #check
  @SimplicialPresheaf.Homology.CechNerve.augmentationMap_isIso

#check @SimplicialPresheaf.Homology.constZeroIso
#check SimplicialPresheaf.Homology.augmentationMap
#check SimplicialObject.Augmented.zeroMap
#check SimplicialObject.Augmented.oneMap
#check SimplicialObject.matchingMap

end CategoryTheory
