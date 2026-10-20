/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.TopCat.Limits.Recognition
import StacksCheckRecall

@[expose] public section

/- Lemma 5.14.3: a cone of topological spaces is limiting when its underlying
cone of types is limiting and projection preimages form a basis. -/
@[stacks 0A2Q]
#check TopCat.Cone.isLimit_of_forgetIsLimit_of_preimageBasis
