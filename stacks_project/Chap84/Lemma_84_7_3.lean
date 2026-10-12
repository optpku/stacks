/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap84.Lemma_84_7_3_Comparison
public import stacks_project.Chap84.Lemma_84_7_3_Homology

/-!
# Lemma 84.7.3

Homology of `π_X^*` and `a_X^*` of a 3-term complex of quasi-coherent
`𝒪_X`-modules: the étale homology sheaf is `ε_{X,*}` of the fppf homology
sheaf, and both have vanishing positive cohomology on affine objects of
`(Spaces/X)_étale`.
-/

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.AssociatedModule

noncomputable section

universe u

/- Lemma 84.7.3 (1): `H_étale = ε_{X,*} H_fppf` as module sheaves on
`(Spaces/X)_étale`. -/
@[stacks 0DGQ] #check etaleHomology_pushforward

/- Lemma 84.7.3 (2): `H^{p+1}_étale(U, H_étale) = 0` for every affine object
`U` of `(Spaces/X)_étale` and every `p : ℕ`. -/
@[stacks 0DGQ] #check etaleHomology_cohomology_isZero

/- Lemma 84.7.3 (3): `H^{p+1}_fppf(U, H_fppf) = 0` for every affine object
`U` of `(Spaces/X)_étale` and every `p : ℕ`. -/
@[stacks 0DGQ] #check fppfHomology_cohomology_isZero

end

end
