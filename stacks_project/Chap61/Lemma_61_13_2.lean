module

public import stacks_project.Chap61.Lemma_61_13_2_Characterization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 61.13.2: let Sch_proétale be a big pro-étale site as in
Definition 61.12.7, and let T = Spec(A) be an affine object of
Sch_proétale. Then A is w-contractible if and only if T is weakly
contractible in Sch_proétale, if and only if every pro-étale covering of T
can be refined by a Zariski covering of the form T = ∐_{i=1,...,n} U_i. -/
@[stacks 098H] #check IsWContractibleRing.tfae_weaklyContractible

#check IsWContractibleRing.iff_isWeaklyContractible
#check IsWContractibleRing.iff_hasFiniteCoproductZariskiRefinement
#check ChosenBigProetaleSite.isWContractibleRing_tfae
