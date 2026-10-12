/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksCheckRecall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-
Lemma 29.2.6: a closed immersion is quasi-compact by the canonical affine-morphism
instance attached to `IsClosedImmersion`.
-/
@[stacks 01QT] #check (AlgebraicGeometry.instQuasiCompactOfIsAffineHom f : QuasiCompact f)

end AlgebraicGeometry
