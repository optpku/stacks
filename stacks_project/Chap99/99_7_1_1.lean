/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap99.«99_7_1_1_Functor»

@[expose] public section

/- 99.7.1.1: the functor of quotients `Q_{F/X/B}` of a quasi-coherent `𝒪_X`-module `F`
along a morphism `f : X ⟶ B` of algebraic spaces over a scheme `S`. It sends a scheme
`T` over `B` to the set of quotients `F_T ⟶ Q` with `Q` quasi-coherent on
`X_T = X ×_B T` and flat over `T`, identifying quotients with the same kernel. -/
@[stacks 082N] #check AlgebraicGeometry.AlgebraicSpace.Quot.functor
