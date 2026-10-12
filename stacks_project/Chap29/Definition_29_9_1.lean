/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import StacksCheckRecall

universe u

/- Definition 29.9.1: A morphism of schemes is surjective exactly when its map on underlying
topological spaces is surjective. -/
@[stacks 01RZ] #check
  (AlgebraicGeometry.surjective_iff :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      AlgebraicGeometry.Surjective f ↔ Function.Surjective f)
