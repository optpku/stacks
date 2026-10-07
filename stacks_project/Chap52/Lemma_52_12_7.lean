module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.LocalCohomology
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace IdealComplement

open CoherentCompletion

/- Lemma 52.12.7: let `U = Spec A ∖ V(𝔞)`. If `f ∈ 𝔞`, `M` is finite,
`A` is `(f)`-adically complete, and powers of `f` annihilate both `H¹_𝔞(M)` and
`H²_𝔞(M)`, then the canonical map from the sections of `(AlgebraicGeometry.tilde M)|_U`
to the inverse limit of its positive `f`-power quotient sections is an isomorphism.
The positive system indexes the quotient by `f ^ (n + 1)` at stage `n`. -/
@[stacks 0EII] #check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.sectionsComparison_bijective_of_localCohomology :
    {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
    (𝔞 : Ideal A) → (f : A) → (hf : f ∈ 𝔞) →
    (M : ModuleCat A) → [Module.Finite A M] →
    [IsAdicComplete (Ideal.span {f}) A] →
    (h_one : Module.IsAnnihilatedByPower (Ideal.span {f})
      ((localCohomology 𝔞 1).obj M)) →
    (h_two : Module.IsAnnihilatedByPower (Ideal.span {f})
      ((localCohomology 𝔞 2).obj M)) →
    let U := idealComplementOpens 𝔞
    Function.Bijective
      (sectionsComparison
        ((idealSheafDataOfIdealOnSpec (Ideal.span {f})).comap U.ι)
        ((tilde M).restrict U.ι)))

end IdealComplement
end AlgebraicGeometry.Scheme.Modules
