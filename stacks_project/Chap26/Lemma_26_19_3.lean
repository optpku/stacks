/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.MorphismProperty.Limits
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

/- Lemma 26.19.3: quasi-compact morphisms are stable under arbitrary base change. -/
@[stacks 01K5] #check quasiCompact_isStableUnderBaseChange
#check CategoryTheory.MorphismProperty.pullback_snd

end AlgebraicGeometry
