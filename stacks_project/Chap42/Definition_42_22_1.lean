/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope
import StacksCheckRecall

universe u

/- Definition 42.22.1: for schemes `Y` and `X`, an envelope is a proper morphism
`f : Y ⟶ X` that is completely decomposed. -/
@[stacks 0GU5] #check
  (AlgebraicGeometry.IsEnvelope : {Y X : AlgebraicGeometry.Scheme.{u}} → (Y ⟶ X) → Prop)
