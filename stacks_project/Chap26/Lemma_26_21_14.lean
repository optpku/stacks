/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

/- Lemma 26.21.14: quasi-compactness descends from `f ≫ g` to `f` when `g` is
quasi-separated. -/
@[stacks 03GI] #check QuasiCompact.of_comp

end AlgebraicGeometry
