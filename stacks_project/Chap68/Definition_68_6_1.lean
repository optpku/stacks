/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap68.Remark_68_17_10_VeryReasonable
public import stacks_project.Chap68.Lemma_68_5_1
import StacksCheckRecall

@[expose] public section

/- Definition 68.6.1 (1): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
We say `X` is decent if for every point `x ∈ |X|` the equivalent conditions of
Lemma 68.4.5 hold, in other words property (γ) of Lemma 68.5.1 holds. -/
@[stacks 03I8] #check AlgebraicGeometry.AlgebraicSpace.IsDecent

/- Definition 68.6.1 (2): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
We say `X` is reasonable if the equivalent conditions of Lemma 68.4.6 hold, in
other words property (δ) of Lemma 68.5.1 holds. -/
@[stacks 03I8] #check AlgebraicGeometry.AlgebraicSpace.IsReasonable

/- Definition 68.6.1 (3): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
We say `X` is very reasonable if the equivalent conditions of Lemma 68.4.7 hold,
i.e., property (ε) of Lemma 68.5.1 holds. -/
@[stacks 03I8] #check AlgebraicGeometry.AlgebraicSpace.IsVeryReasonable

#check AlgebraicGeometry.AlgebraicSpace.isDecent_iff_forallAffineEtaleFiniteAbove
