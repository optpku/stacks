/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap84.Lemma_84_7_4_Comparison

/-!
# Lemma 84.7.4

For an object of `D_QCoh(𝒪_X)` on an algebraic space, the canonical maps
`Lπ_X^* K ⟶ Rε_{X,*}(La_X^* K)` and `K ⟶ Ra_{X,*}(La_X^* K)` are isomorphisms.
-/

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.AssociatedModule

noncomputable section

universe u

/- Lemma 84.7.4 (1): the canonical map `Lπ_X^* K ⟶ Rε_{X,*}(La_X^* K)` is an
isomorphism. -/
@[stacks 0DGR] #check piPullbackDerivedUnit_isIso

/- Lemma 84.7.4 (2): the canonical map `K ⟶ Ra_{X,*}(La_X^* K)` is an
isomorphism. -/
@[stacks 0DGR] #check aDerivedUnit_isIso

end

end
