/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Product
import StacksCheckRecall

namespace CategoryTheory

/- Lemma 25.7.2 [stacks 01GI]: the binary product of two hypercoverings of one target is again
a hypercovering. The neutral construction and its underlying-simplicial computation are owned by
`CategoryTheory.Hypercovering.prod` and `CategoryTheory.Hypercovering.prod_toSimplicialObject`. -/
@[stacks 01GI] #check @Hypercovering.prod
#check @Hypercovering.prod_toSimplicialObject

end CategoryTheory
