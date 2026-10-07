module

import StacksCheckRecall
public import ReasLib.RingTheory.Ideal.MinimalGenerators

@[expose] public section

/- Lemma 23.7.4 (tag `09PV`): for proper ideals `I ≤ J` in a
Noetherian local ring, finite Tor dimension of `A / J` over `A / I` makes
`I / 𝔪 I → J / 𝔪 J` injective.  The reusable theorem omits the redundant
assumption `I ≠ ⊤`, which follows from `I ≤ J` and `J ≠ ⊤`. -/
universe u

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {I J : Ideal A}
variable (hJ : J ≠ ⊤) (hIJ : I ≤ J)
variable (hTor : (Ideal.Quotient.factor hIJ).HasFiniteTorDimension)

@[stacks 09PV]
#check (Ideal.quotientMapByMaximalIdeal_injective_of_finiteTorDimension hJ hIJ hTor :
  Function.Injective
    ((Submodule.inclusion hIJ).quotientMapByIdeal (IsLocalRing.maximalIdeal A)))

end
