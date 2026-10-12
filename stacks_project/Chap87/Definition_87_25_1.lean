/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Definition_87_25_1_Surjective
import StacksCheckRecall

@[expose] public section

/- Definition 87.25.1: a morphism `f : X ⟶ Y` of formal algebraic spaces over a
scheme `S` is surjective if it induces a surjective morphism
`reduction X ⟶ reduction Y` of underlying reduced algebraic spaces. -/
@[stacks 0GHP] #check AlgebraicGeometry.FormalAlgebraicSpace.Surjective
