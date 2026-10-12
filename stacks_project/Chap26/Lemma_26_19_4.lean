/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

/- Lemma 26.19.4: compositions of quasi-compact morphisms are quasi-compact. -/
@[stacks 01K6] #check quasiCompact_comp

end AlgebraicGeometry
