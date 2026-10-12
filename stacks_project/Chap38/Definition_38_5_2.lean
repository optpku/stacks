/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageAtAmbientPoint
import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageAt
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 38.5.2: a complete dévissage of `ℱ / X / S` at `x` is a nonempty finite
chain of one-step dévissages at chosen points, in which each successor treats the cokernel
of the preceding comparison map and the final comparison map has zero cokernel. -/
@[stacks 05HI] #check
  (AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint :
    {S X : Scheme.{u}} → (f : X ⟶ S) → (F : X.Modules) →
      [LocallyOfFiniteType f] → [F.IsQuasicoherent] → [F.IsFiniteType] →
        (x : X) → Type (u + 1))
