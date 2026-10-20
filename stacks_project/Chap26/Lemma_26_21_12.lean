/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Separated.Product
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

/- Lemma 26.21.12 (1): separated morphisms are stable under composition. -/
@[stacks 01KU] #check IsSeparated.stableUnderComposition

/- Lemma 26.21.12 (2): quasi-separated morphisms are stable under composition. -/
@[stacks 01KU] #check quasiSeparated_isStableUnderComposition
#check quasiSeparated_comp

/- Lemma 26.21.12 (3): separated morphisms are stable under base change. -/
@[stacks 01KU] #check IsSeparated.isStableUnderBaseChange

/- Lemma 26.21.12 (4): quasi-separated morphisms are stable under base change. -/
@[stacks 01KU] #check quasiSeparated_isStableUnderBaseChange

/- Lemma 26.21.12 (5) and (6): the corresponding binary product maps are available as
instances. -/
@[stacks 01KU] #check isSeparated_overProdMap
@[stacks 01KU] #check quasiSeparated_overProdMap

end AlgebraicGeometry
