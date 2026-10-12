/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.PullbackCarrier
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory.Limits

universe u

/- Lemma 29.9.4: the base change of a surjective morphism is surjective. -/
@[stacks 01S1] #check
  (@AlgebraicGeometry.Surjective.instSndScheme :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Surjective f],
      Surjective (pullback.snd f g))
