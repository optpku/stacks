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

/- Lemma 26.19.8: a quasi-compact morphism is closed exactly when specializations lift. -/
@[stacks 01K9] #check isClosedMap_iff_specializingMap

end AlgebraicGeometry
