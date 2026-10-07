module

public import stacks_project.Chap61.Lemma_61_11_2_Characterization
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 61.11.2: for a commutative ring `A`, the following are equivalent:
`A` is w-contractible, every faithfully flat ind-étale ring map `A →+* B` has
a retraction, and `PrimeSpectrum A` is w-local with
`ConnectedComponents (PrimeSpectrum A)` extremally disconnected and
`Localization.AtPrime m` strictly henselian at every maximal ideal `m`. -/
@[stacks 0982] #check IsWContractibleRing.tfae

#check IsWContractibleRing.iff_hasFaithfullyFlatIndEtaleRetraction
#check IsWContractibleRing.iff_wLocal_extremallyDisconnected_strictlyHenselian
