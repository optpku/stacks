module

public import stacks_project.Chap58.Lemma_58_24_1

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.PuncturedSpectrum
open IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable (f : maximalIdeal A)

/-- Lemma 58.25.1: in Situation 58.19.1, if `A` has a dualizing complex and is
`f`-adically complete, the Lemma 58.23.1 neighborhood alternative holds, purity
holds at `(A_f)_p` for every maximal ideal `p` of `A_f`, and purity holds for
`A`, then purity holds for `A ⧸ principalIdeal f`. -/
@[stacks 0DXZ, instance]
instance hasPurity_principalQuotient_of_dualizing_complete
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))]
    [Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)]
    [IsAdicComplete (principalIdeal f) A]
    [Fact (dualizingCompleteNeighborhoodAlternative f)]
    [Fact (hasPurityAtMaximalsAway f)]
    [HasPurity A] :
    HasPurity (A ⧸ principalIdeal f) := sorry

end AlgebraicGeometry.PuncturedSpectrum
