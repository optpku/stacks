/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 29.11.10: a closed immersion is an affine morphism. -/
@[stacks 01SE] #check (@AlgebraicGeometry.IsClosedImmersion.instIsAffineHom :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f], IsAffineHom f)

end AlgebraicGeometry
