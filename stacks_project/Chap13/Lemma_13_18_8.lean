/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.DerivedCategory.KInjective.Bounded
import StacksCheckRecall

@[expose] public section

/- Lemma 13.18.8 is the bounded-below injective view of Mathlib's canonical
homotopy-to-derived map bijection. -/
@[stacks 05TG] #check @CochainComplex.IsKInjective.Qh_map_bijective
@[stacks 05TG] #check @CochainComplex.InjectivePlus.toDerived_map_bijective

end
