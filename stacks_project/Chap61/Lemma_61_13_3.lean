module

public import stacks_project.Chap61.Lemma_61_13_3_Cover
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u v

/- Lemma 61.13.3: let Sch_proétale be a big pro-étale site as in
Definition 61.12.7. For every object T of Sch_proétale there exists a
covering {T_i ⟶ T} in Sch_proétale with each T_i affine and the spectrum
of a w-contractible ring. In particular, T_i is weakly contractible in
Sch_proétale. -/
@[stacks 098I] #check ChosenBigProetaleSite.exists_affine_wContractibleRing_cover

#check ChosenBigProetaleSite.exists_affine_weaklyContractible_cover
#check ChosenBigProetaleSite.hasEnough_isAffine_isWContractibleRing
#check Scheme.Proetale.exists_affine_wContractibleRing_cover
#check Scheme.Proetale.exists_affineCover_isWContractibleRing
