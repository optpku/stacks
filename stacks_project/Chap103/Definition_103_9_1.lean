/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap103.Definition_103_9_1_Parasitic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- Definition 103.9.1: let `X` be an algebraic stack. A presheaf of
`𝒪_X`-modules `F` is parasitic if `F(x) = 0` for any object `x` of `X`
which lies over a scheme `U` such that the corresponding morphism
`x : U ⟶ X` is flat. -/
@[stacks 0773] #check AlgebraicGeometry.GroupoidsOver.IsParasitic
