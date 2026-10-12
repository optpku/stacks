/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.25.12: a quasi-compact, surjective, flat morphism of schemes is submersive.
Equivalently, its underlying map is a quotient map, so a subset of the target is open or closed
exactly when its inverse image is open or closed. -/
@[stacks 02JY] #check
  (AlgebraicGeometry.Flat.isQuotientMap_of_surjective :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f]
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.Surjective f],
      Topology.IsQuotientMap f)
