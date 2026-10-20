/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

/- Lemma 26.20.2: universal closedness is universal specialization lifting together with the
canonical quasi-compactness condition. -/
@[stacks 01KC] #check universallyClosed_eq_universallySpecializing

end AlgebraicGeometry
