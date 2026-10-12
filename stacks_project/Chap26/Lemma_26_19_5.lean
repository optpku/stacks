/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/- Lemma 26.19.5: a closed immersion is quasi-compact. -/
@[stacks 01K7] #check (inferInstance : QuasiCompact f)

end AlgebraicGeometry
