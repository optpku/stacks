module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Sections
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Basic
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.RingTheory.AdicCompletion.Basic

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace IdealComplement

open CoherentCompletion

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- For a finite module over a Noetherian `(f)`-adically complete ring, if `f ∈ 𝔞`
and powers of `f` annihilate both `H¹_𝔞(M)` and `H²_𝔞(M)`, the canonical map from
sections of `(AlgebraicGeometry.tilde M)|_U` on `U = Spec A ∖ V(𝔞)` to the inverse
limit of its positive `f`-power quotient sections is bijective. The quotient at
stage `n` is by `f ^ (n + 1)`. -/
theorem sectionsComparison_bijective_of_localCohomology
    (𝔞 : Ideal A) (f : A) (hf : f ∈ 𝔞)
    (M : ModuleCat A) [Module.Finite A M]
    [IsAdicComplete (Ideal.span {f}) A]
    (h_one : Module.IsAnnihilatedByPower (Ideal.span {f})
      ((localCohomology 𝔞 1).obj M))
    (h_two : Module.IsAnnihilatedByPower (Ideal.span {f})
      ((localCohomology 𝔞 2).obj M)) :
    let U := idealComplementOpens 𝔞
    Function.Bijective
      (sectionsComparison
        ((idealSheafDataOfIdealOnSpec (Ideal.span {f})).comap U.ι)
        ((tilde M).restrict U.ι)) := sorry

/-- For a Noetherian `(f)`-adically complete ring, if `f ∈ 𝔞` and powers of
`f` annihilate the first two local cohomology modules supported on `𝔞`,
completion along `(f)` on `Spec A ∖ V(𝔞)` is fully faithful on finite locally
free coherent modules. -/
theorem completionFullyFaithful_of_localCohomology
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (𝔞 : Ideal A) (f : A) (hf : f ∈ 𝔞)
    [IsAdicComplete (Ideal.span {f}) A]
    (h_one : Module.IsAnnihilatedByPower (Ideal.span {f})
      ((localCohomology 𝔞 1).obj (ModuleCat.of A A)))
    (h_two : Module.IsAnnihilatedByPower (Ideal.span {f})
      ((localCohomology 𝔞 2).obj (ModuleCat.of A A))) :
    let U := idealComplementOpens 𝔞
    Nonempty (CoherentCompletion.onFiniteLocallyFree
      ((idealSheafDataOfIdealOnSpec (Ideal.span {f})).comap U.ι)).FullyFaithful := sorry

end IdealComplement
end AlgebraicGeometry.Scheme.Modules
