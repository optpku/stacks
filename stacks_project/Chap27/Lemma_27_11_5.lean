module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.ClosedImmersion

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {P𝒜 : ProjTwistPresentation 𝒜} {Pℬ : ProjTwistPresentation ℬ}
  {ψ : 𝒜 →+*ᵍ ℬ}

/- Lemma 27.11.5 (1): eventual degreewise surjectivity makes the natural map domain all of
`Proj ℬ`. -/
@[stacks 01N1] #check
  (AlgebraicGeometry.projMapDomain_eq_top_of_eventually_surjective :
    (∃ N : ℕ, ∀ d ≥ N, Function.Surjective (ψ.gradedAddHom d)) →
      projMapDomain ψ = ⊤)

/- The induced map on the full target projective spectrum is a closed immersion. -/
#check
  (AlgebraicGeometry.projMap_isClosedImmersion_of_eventually_surjective :
    (hψsurj : ∃ N : ℕ, ∀ d ≥ N, Function.Surjective (ψ.gradedAddHom d)) →
      let hU : projMapDomain ψ = ⊤ :=
        AlgebraicGeometry.projMapDomain_eq_top_of_eventually_surjective hψsurj
      IsClosedImmersion
        (AlgebraicGeometry.projMapOnTarget ψ (projMap P𝒜 Pℬ ψ).map hU))

/- If the source is generated in degree one over degree zero, each integral-twist comparison
on the full target projective spectrum is an isomorphism. -/
#check
  (AlgebraicGeometry.ProjMap.thetaOnTarget_isIso_of_degreeOneGenerated
    P𝒜 Pℬ :
    (hψsurj : ∃ N : ℕ, ∀ d ≥ N, Function.Surjective (ψ.gradedAddHom d)) →
      Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤ →
        (n : ℤ) →
          let hU : projMapDomain ψ = ⊤ :=
            AlgebraicGeometry.projMapDomain_eq_top_of_eventually_surjective hψsurj
          let hi : AlgebraicGeometry.projMapDomainTopInclusion ψ hU ≫
              (projMapDomain ψ).ι = 𝟙 (Proj ℬ) :=
            AlgebraicGeometry.projMapDomainTopInclusion_comp_ι ψ hU
          IsIso (AlgebraicGeometry.projMapThetaOnTarget ψ (P𝒜.actualTwist n)
            (Pℬ.actualTwist n) (projMap P𝒜 Pℬ ψ).map
              ((projMap P𝒜 Pℬ ψ).theta n) hU hi))

end

end AlgebraicGeometry
