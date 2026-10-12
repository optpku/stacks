/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_13_12_ResidualSpace
public import stacks_project.Chap68.Lemma_68_13_5
import StacksCheckRecall

@[expose] public section

/- Definition 68.13.6: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `x ∈ |X|`. The residual space of `X` at `x` is the monomorphism `Z_x ⟶ X`
constructed in Lemma 68.13.5. -/
@[stacks 06R0] #check AlgebraicGeometry.AlgebraicSpace.IsResidualSpace
#check AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.exists_at
#check AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.existsUnique_iso
