/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Definition_68_24_2_Unibranch
import StacksCheckRecall

@[expose] public section

/- Definition 68.24.2 (1): Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x ∈ |X|`. We say that `X` is unibranch at `x` if the equivalent conditions of
Lemma 68.24.1 hold. -/
@[stacks 0DQ7] #check AlgebraicGeometry.AlgebraicSpace.isUnibranchAt

/- Definition 68.24.2 (2): Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
We say that `X` is unibranch if `X` is unibranch at every `x ∈ |X|`. -/
@[stacks 0DQ7] #check AlgebraicGeometry.AlgebraicSpace.isUnibranch

#check AlgebraicGeometry.AlgebraicSpace.isUnibranchAt_iff_uniqueMinimalPrime
#check AlgebraicGeometry.AlgebraicSpace.isUnibranch_iff
