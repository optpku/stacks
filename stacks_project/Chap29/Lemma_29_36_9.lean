/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.36.9: any open immersion is étale. -/
@[stacks 02GP] #check
  (AlgebraicGeometry.Etale.instOfIsOpenImmersion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f], Etale f)
