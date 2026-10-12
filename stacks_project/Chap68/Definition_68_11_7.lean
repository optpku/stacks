/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing
import StacksCheckRecall

open AlgebraicGeometry

/- Definition 68.11.7: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x ∈ |X|`. The henselian local ring of `X` at `x` is
`henselianLocalRing X x = colim Γ(U, 𝒪_U)`, where the colimit is over the elementary
étale neighbourhoods `(U, u) ⟶ (X, x)`. -/
@[stacks 0BGW] #check AlgebraicSpace.henselianLocalRing
