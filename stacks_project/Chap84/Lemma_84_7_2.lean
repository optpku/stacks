/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap84.Lemma_84_7_2_Comparison

/-!
# Lemma 84.7.2

For a quasi-coherent module on an algebraic space, the canonical maps
`π_X^* F ⟶ Rε_{X,*}(a_X^* F)` and `F ⟶ Ra_{X,*}(a_X^* F)` are isomorphisms.
-/

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.AssociatedModule

noncomputable section

universe u

/- Lemma 84.7.2 (1): the canonical map `π_X^* F ⟶ Rε_{X,*}(a_X^* F)` is an
isomorphism. -/
@[stacks 0DGP] #check piPullbackToEpsilonDerived_isIso

/- Lemma 84.7.2 (2): the canonical map `F ⟶ Ra_{X,*}(a_X^* F)` is an
isomorphism. -/
@[stacks 0DGP] #check toADerived_isIso

end

end
