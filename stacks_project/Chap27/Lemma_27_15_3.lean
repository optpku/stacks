module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.AffineOpenComposition
public import stacks_project.Chap27.Lemma_27_15_2

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {S : Scheme.{u}}
variable {U U' U'' : S.affineOpens}
variable {A A' A'' σ τ ω : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing A'] [SetLike τ A'] [AddSubgroupClass τ A']
variable [CommRing A''] [SetLike ω A''] [AddSubgroupClass ω A'']
variable (sectionGradingU : ℕ → σ) [GradedRing sectionGradingU]
variable (sectionGradingU' : ℕ → τ) [GradedRing sectionGradingU']
variable (sectionGradingU'' : ℕ → ω) [GradedRing sectionGradingU'']
variable (PSectionU : ProjTwistPresentation sectionGradingU)
variable (PSectionU' : ProjTwistPresentation sectionGradingU')
variable (PSectionU'' : ProjTwistPresentation sectionGradingU'')

/- Lemma 27.15.3: for three nested affine opens, the projective-spectrum map induced by direct
restriction is the composite of the maps induced by successive restrictions. -/
@[stacks 01NP] #check
  (AlgebraicGeometry.affineOpenSectionProj_map_comp
      sectionGradingU sectionGradingU' sectionGradingU''
      PSectionU PSectionU' PSectionU'' :
    ∀ (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
      (hqc : ∀ n : ℤ, (𝒜 n).IsQuasicoherent)
      (h : (U : S.Opens) ≤ (U' : S.Opens))
      (h' : (U' : S.Opens) ≤ (U'' : S.Opens))
      (sectionGradingIsoU :
        ∀ d : ℕ, (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGradingU d)
      (sectionGradingIsoU' :
        ∀ d : ℕ, (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U' : S.Opens)) ≃ sectionGradingU' d)
      (sectionGradingIsoU'' :
        ∀ d : ℕ, (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U'' : S.Opens)) ≃ sectionGradingU'' d)
      (sectionRestrictU'U : sectionGradingU' →+*ᵍ sectionGradingU)
      (sectionRestrictU'U_spec :
        ∀ d : ℕ, ∀ x : sectionGradingU' d,
          sectionGradingIsoU d
              ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom)
                ((sectionGradingIsoU' d).symm x)) =
            (sectionRestrictU'U.gradedAddHom d) x)
      (sectionRestrictU''U' : sectionGradingU'' →+*ᵍ sectionGradingU')
      (sectionRestrictU''U'_spec :
        ∀ d : ℕ, ∀ x : sectionGradingU'' d,
          sectionGradingIsoU' d
              ((((𝒜 (Int.ofNat d)).val.map (homOfLE h').op).hom)
                ((sectionGradingIsoU'' d).symm x)) =
            (sectionRestrictU''U'.gradedAddHom d) x)
      (sectionRestrictU''U : sectionGradingU'' →+*ᵍ sectionGradingU)
      (sectionRestrictU''U_spec :
        ∀ d : ℕ, ∀ x : sectionGradingU'' d,
          sectionGradingIsoU d
              ((((𝒜 (Int.ofNat d)).val.map (homOfLE (h.trans h')).op).hom)
                ((sectionGradingIsoU'' d).symm x)) =
            (sectionRestrictU''U.gradedAddHom d) x)
      (sectionProjDomainTopU'U : projMapDomain sectionRestrictU'U = ⊤)
      (sectionProjDomainTopU''U' : projMapDomain sectionRestrictU''U' = ⊤)
      (sectionProjDomainTopU''U : projMapDomain sectionRestrictU''U = ⊤),
      projMapOnTarget sectionRestrictU''U
          (projMap PSectionU'' PSectionU sectionRestrictU''U).map sectionProjDomainTopU''U =
        projMapOnTarget sectionRestrictU'U
            (projMap PSectionU' PSectionU sectionRestrictU'U).map sectionProjDomainTopU'U ≫
          projMapOnTarget sectionRestrictU''U'
            (projMap PSectionU'' PSectionU' sectionRestrictU''U').map
            sectionProjDomainTopU''U')

/- The corresponding integral-twist comparison for direct restriction is the transported
pullback composite of the comparisons for the two successive restrictions. -/
#check
  (AlgebraicGeometry.affineOpenSectionProj_theta_comp
      sectionGradingU sectionGradingU' sectionGradingU''
      PSectionU PSectionU' PSectionU'' :
    ∀ (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
      (hqc : ∀ n : ℤ, (𝒜 n).IsQuasicoherent)
      (h : (U : S.Opens) ≤ (U' : S.Opens))
      (h' : (U' : S.Opens) ≤ (U'' : S.Opens))
      (sectionGradingIsoU :
        ∀ d : ℕ, (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGradingU d)
      (sectionGradingIsoU' :
        ∀ d : ℕ, (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U' : S.Opens)) ≃ sectionGradingU' d)
      (sectionGradingIsoU'' :
        ∀ d : ℕ, (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U'' : S.Opens)) ≃ sectionGradingU'' d)
      (sectionRestrictU'U : sectionGradingU' →+*ᵍ sectionGradingU)
      (sectionRestrictU'U_spec :
        ∀ d : ℕ, ∀ x : sectionGradingU' d,
          sectionGradingIsoU d
              ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom)
                ((sectionGradingIsoU' d).symm x)) =
            (sectionRestrictU'U.gradedAddHom d) x)
      (sectionRestrictU''U' : sectionGradingU'' →+*ᵍ sectionGradingU')
      (sectionRestrictU''U'_spec :
        ∀ d : ℕ, ∀ x : sectionGradingU'' d,
          sectionGradingIsoU' d
              ((((𝒜 (Int.ofNat d)).val.map (homOfLE h').op).hom)
                ((sectionGradingIsoU'' d).symm x)) =
            (sectionRestrictU''U'.gradedAddHom d) x)
      (sectionRestrictU''U : sectionGradingU'' →+*ᵍ sectionGradingU)
      (sectionRestrictU''U_spec :
        ∀ d : ℕ, ∀ x : sectionGradingU'' d,
          sectionGradingIsoU d
              ((((𝒜 (Int.ofNat d)).val.map (homOfLE (h.trans h')).op).hom)
                ((sectionGradingIsoU'' d).symm x)) =
            (sectionRestrictU''U.gradedAddHom d) x)
      (sectionProjDomainTopU'U : projMapDomain sectionRestrictU'U = ⊤)
      (sectionProjDomainTopU''U' : projMapDomain sectionRestrictU''U' = ⊤)
      (sectionProjDomainTopU''U : projMapDomain sectionRestrictU''U = ⊤),
      ∀ n : ℤ,
        let r :=
          projMapOnTarget sectionRestrictU'U
            (projMap PSectionU' PSectionU sectionRestrictU'U).map sectionProjDomainTopU'U
        let r' :=
          projMapOnTarget sectionRestrictU''U'
            (projMap PSectionU'' PSectionU' sectionRestrictU''U').map
            sectionProjDomainTopU''U'
        let hcomp :
            projMapOnTarget sectionRestrictU''U
                (projMap PSectionU'' PSectionU sectionRestrictU''U).map
                sectionProjDomainTopU''U =
              r ≫ r' :=
          affineOpenSectionProj_map_comp
            sectionGradingU sectionGradingU' sectionGradingU''
            PSectionU PSectionU' PSectionU''
            𝒜 hqc h h'
            sectionGradingIsoU sectionGradingIsoU' sectionGradingIsoU''
            sectionRestrictU'U sectionRestrictU'U_spec
            sectionRestrictU''U' sectionRestrictU''U'_spec
            sectionRestrictU''U sectionRestrictU''U_spec
            sectionProjDomainTopU'U sectionProjDomainTopU''U' sectionProjDomainTopU''U
        projMapThetaOnTarget sectionRestrictU''U
            (PSectionU''.actualTwist n) (PSectionU.actualTwist n)
            (projMap PSectionU'' PSectionU sectionRestrictU''U).map
            ((projMap PSectionU'' PSectionU sectionRestrictU''U).theta n)
            sectionProjDomainTopU''U
            (projMapDomainTopInclusion_comp_ι sectionRestrictU''U sectionProjDomainTopU''U) =
          ((Scheme.Modules.pullbackCongr hcomp).hom.app (PSectionU''.actualTwist n)) ≫
            ((Scheme.Modules.pullbackComp r r').inv.app (PSectionU''.actualTwist n)) ≫
            (Scheme.Modules.pullback r).map
              (projMapThetaOnTarget sectionRestrictU''U'
                (PSectionU''.actualTwist n) (PSectionU'.actualTwist n)
                (projMap PSectionU'' PSectionU' sectionRestrictU''U').map
                ((projMap PSectionU'' PSectionU' sectionRestrictU''U').theta n)
                sectionProjDomainTopU''U'
                (projMapDomainTopInclusion_comp_ι
                  sectionRestrictU''U' sectionProjDomainTopU''U')) ≫
            projMapThetaOnTarget sectionRestrictU'U
              (PSectionU'.actualTwist n) (PSectionU.actualTwist n)
              (projMap PSectionU' PSectionU sectionRestrictU'U).map
              ((projMap PSectionU' PSectionU sectionRestrictU'U).theta n)
              sectionProjDomainTopU'U
              (projMapDomainTopInclusion_comp_ι sectionRestrictU'U sectionProjDomainTopU'U))

end

end AlgebraicGeometry
