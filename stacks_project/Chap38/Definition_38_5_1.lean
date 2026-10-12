/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageOver
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Definition 38.5.1: a complete dévissage of `F / X / S` over `s` is a finite nonempty
sequence of one-step dévissages whose comparison maps are isomorphisms at the unique generic
points of the fibres and whose final comparison has zero cokernel. -/
@[stacks 05HH] #check (AlgebraicGeometry.Scheme.Modules.CompleteDevissageOver :
  {S X : Scheme.{u}} → (f : X ⟶ S) → (F : X.Modules) →
    [LocallyOfFiniteType f] → [F.IsQuasicoherent] → [F.IsFiniteType] →
      (s : S) → Type (u + 1))
