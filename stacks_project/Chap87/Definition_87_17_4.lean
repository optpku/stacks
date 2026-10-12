/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Definition_87_17_4_QuasiCompact
import StacksCheckRecall

@[expose] public section

/- Definition 87.17.4: a morphism `f : X ⟶ Y` of formal algebraic spaces over a
scheme `S` is quasi-compact if the equivalent conditions of Lemma 87.17.3 hold,
equivalently if `mapReduction f` is a quasi-compact morphism of algebraic
spaces. -/
@[stacks 0AJC] #check AlgebraicGeometry.FormalAlgebraicSpace.QuasiCompact
