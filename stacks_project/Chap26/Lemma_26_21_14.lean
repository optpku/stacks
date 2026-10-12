/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
