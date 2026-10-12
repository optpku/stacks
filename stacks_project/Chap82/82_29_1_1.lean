/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap82.«82_29_1_1_Tensor»

/- 82.29.1.1: In Situation 82.2.1, for good `X / B`, a finite locally free
`𝒪_X`-module `E` of rank `r`, and an invertible `𝒪_X`-module `L`, the identity
`c_i(E ⊗ L) = ∑ j, Nat.choose (r + j - i) j • c_{i-j}(E) * c_1(L)^j`
holds in Chow cohomology `A^*(X)` of `X` relative to `f` and `δ`. -/
@[stacks 0ES5] #check AlgebraicGeometry.AlgebraicSpace.chernClass_tensor_invertible
