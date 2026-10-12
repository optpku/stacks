/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 29.36.3: The composition of two morphisms which are étale is étale. -/
@[stacks 02GN] #check
  (AlgebraicGeometry.Etale.etale_comp :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {Z : Scheme.{u}} (g : Y ⟶ Z)
      [Etale f] [Etale g], Etale (f ≫ g))
