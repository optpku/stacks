/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
import StacksCheckRecall

@[expose] public section

/- Definition 67.31.2 (1): let `S` be a scheme, `f : X ⟶ Y` a morphism of algebraic
spaces over `S`, and `F` a quasi-coherent sheaf on `X`. For `x ∈ |X|` (`Points X`),
we say `F` is flat at `x` over `Y` if the equivalent conditions of Lemma 67.31.1 hold. -/
@[stacks 05VV] #check AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAt

/- Definition 67.31.2 (2): with the same standing data, we say `F` is flat over `Y`
if `F` is flat over `Y` at every `x ∈ |X|`. -/
@[stacks 05VV] #check AlgebraicGeometry.AlgebraicSpace.Modules.flatOver
