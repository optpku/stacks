/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Presheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

namespace CategoryTheory

/- Lemma 25.4.5 [stacks 01GF], positive-degree clause. -/
@[stacks 01GF "positive degrees"] #check
  @Hypercovering.Homology.succ_isZero

/- Lemma 25.4.5 [stacks 01GF], degree-zero augmentation clause. -/
@[stacks 01GF "degree zero"] #check
  @Hypercovering.Homology.augmentationMap_isIso

#check Hypercovering.simplicialPresheaf
#check Hypercovering.augmentation

end CategoryTheory
