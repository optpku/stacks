module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.LocalCohomology
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace IdealComplement

open CoherentCompletion

/-
Lemma 52.15.5: for `U = Spec A ∖ V(𝔞)`, if `A` is `(f)`-adically complete
and powers of `f` annihilate both `H¹_𝔞(A)` and `H²_𝔞(A)`, then completion along
`(f)` on `U` is fully faithful on finite locally free coherent modules.
-/
@[stacks 0EKS]
#check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.completionFullyFaithful_of_localCohomology :
    {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
      (𝔞 : Ideal A) → (f : A) → f ∈ 𝔞 →
      [IsAdicComplete (Ideal.span {f}) A] →
      Module.IsAnnihilatedByPower (Ideal.span {f})
        ((localCohomology 𝔞 1).obj (ModuleCat.of A A)) →
      Module.IsAnnihilatedByPower (Ideal.span {f})
        ((localCohomology 𝔞 2).obj (ModuleCat.of A A)) →
      let U := idealComplementOpens 𝔞
      Nonempty (CoherentCompletion.onFiniteLocallyFree
        ((idealSheafDataOfIdealOnSpec (Ideal.span {f})).comap U.ι)).FullyFaithful)

end IdealComplement
end AlgebraicGeometry.Scheme.Modules
