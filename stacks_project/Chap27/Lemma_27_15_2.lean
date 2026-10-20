/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.AffineOpenBaseChange

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The morphism of projective spectra induced by a graded restriction map whose natural
projective-spectrum domain is the whole target. -/
abbrev affineOpenSectionProjMap
    {A A' sigma tau : Type u}
    [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
    [CommRing A'] [SetLike tau A'] [AddSubgroupClass tau A']
    {calA : ℕ → sigma} {calA' : ℕ → tau} [GradedRing calA] [GradedRing calA']
    (PcalA' : ProjTwistPresentation calA')
    (PcalA : ProjTwistPresentation calA)
    (sectionRestrict : calA' →+*ᵍ calA)
    (hTop : projMapDomain sectionRestrict = ⊤) :
    Proj calA ⟶ Proj calA' :=
  projMapOnTarget sectionRestrict (projMap PcalA' PcalA sectionRestrict).map hTop

/-- The integral-twist comparison transported along a graded restriction map whose natural
projective-spectrum domain is the whole target. -/
abbrev affineOpenSectionProjTheta
    {A A' sigma tau : Type u}
    [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
    [CommRing A'] [SetLike tau A'] [AddSubgroupClass tau A']
    {calA : ℕ → sigma} {calA' : ℕ → tau} [GradedRing calA] [GradedRing calA']
    (PcalA' : ProjTwistPresentation calA')
    (PcalA : ProjTwistPresentation calA)
    (sectionRestrict : calA' →+*ᵍ calA)
    (hTop : projMapDomain sectionRestrict = ⊤)
    (n : ℤ) :
    (Scheme.Modules.pullback
      (affineOpenSectionProjMap PcalA' PcalA sectionRestrict hTop)).obj
        (PcalA'.actualTwist n) ⟶ PcalA.actualTwist n :=
  projMapThetaOnTarget sectionRestrict
    (PcalA'.actualTwist n) (PcalA.actualTwist n)
    (projMap PcalA' PcalA sectionRestrict).map
    ((projMap PcalA' PcalA sectionRestrict).theta n) hTop
    (projMapDomainTopInclusion_comp_ι sectionRestrict hTop)

end AlgebraicGeometry

/- Lemma 27.15.2 (1): for nested affine opens, the projective spectra of compatible
quasi-coherent section-ring models form a cartesian square over those opens. -/
@[stacks 01NO] #check
  (AlgebraicGeometry.AffineOpenSectionProj.isPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U U' : S.affineOpens}
      {A A' sigma tau : Type u}
      [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
      [CommRing A'] [SetLike tau A'] [AddSubgroupClass tau A']
      (calA : ℕ → sigma) [GradedRing calA]
      (calA' : ℕ → tau) [GradedRing calA']
      (h : (U : S.Opens) ≤ (U' : S.Opens))
      (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
      [𝒜.IsCommutative]
      (hqc : 𝒜.IsQuasicoherent)
      (model : ∀ d : ℕ,
        (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ calA d)
      (model' : ∀ d : ℕ,
        (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U' : S.Opens)) ≃+ calA' d)
      (hModel : AlgebraicGeometry.AffineOpenSectionProj.IsAffineOpenSectionModel
        calA 𝒜 U model)
      (hModel' : AlgebraicGeometry.AffineOpenSectionProj.IsAffineOpenSectionModel
        calA' 𝒜 U' model')
      (PcalA : AlgebraicGeometry.ProjTwistPresentation calA)
      (PcalA' : AlgebraicGeometry.ProjTwistPresentation calA')
      (sectionRestrict : calA' →+*ᵍ calA)
      (sectionRestrict_spec :
        ∀ d : ℕ, ∀ x : calA' d,
          model d
              ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom)
                ((model' d).symm x)) =
            (sectionRestrict.gradedAddHom d) x),
      let hTop := AlgebraicGeometry.AffineOpenSectionProj.domain_eq_top
        calA calA' h 𝒜 hqc model model' hModel hModel' sectionRestrict sectionRestrict_spec
      CategoryTheory.IsPullback
        (AlgebraicGeometry.projMapOnTarget sectionRestrict
          (AlgebraicGeometry.projMap PcalA' PcalA sectionRestrict).map hTop)
        (AlgebraicGeometry.AffineOpenSectionProj.toAffineOpen calA 𝒜 U model hModel)
        (AlgebraicGeometry.AffineOpenSectionProj.toAffineOpen calA' 𝒜 U' model' hModel')
        (S.homOfLE h))

/- Lemma 27.15.2 (2): every integral-twist comparison transported to the full projective
spectrum is an isomorphism. -/
@[stacks 01NO] #check
  (AlgebraicGeometry.AffineOpenSectionProj.theta_isIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U U' : S.affineOpens}
      {A A' sigma tau : Type u}
      [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
      [CommRing A'] [SetLike tau A'] [AddSubgroupClass tau A']
      (calA : ℕ → sigma) [GradedRing calA]
      (calA' : ℕ → tau) [GradedRing calA']
      (h : (U : S.Opens) ≤ (U' : S.Opens))
      (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
      [𝒜.IsCommutative]
      (hqc : 𝒜.IsQuasicoherent)
      (model : ∀ d : ℕ,
        (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ calA d)
      (model' : ∀ d : ℕ,
        (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U' : S.Opens)) ≃+ calA' d)
      (hModel : AlgebraicGeometry.AffineOpenSectionProj.IsAffineOpenSectionModel
        calA 𝒜 U model)
      (hModel' : AlgebraicGeometry.AffineOpenSectionProj.IsAffineOpenSectionModel
        calA' 𝒜 U' model')
      (PcalA : AlgebraicGeometry.ProjTwistPresentation calA)
      (PcalA' : AlgebraicGeometry.ProjTwistPresentation calA')
      (sectionRestrict : calA' →+*ᵍ calA)
      (sectionRestrict_spec :
        ∀ d : ℕ, ∀ x : calA' d,
          model d
              ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom)
                ((model' d).symm x)) =
            (sectionRestrict.gradedAddHom d) x)
      (n : ℤ),
      let hTop := AlgebraicGeometry.AffineOpenSectionProj.domain_eq_top
        calA calA' h 𝒜 hqc model model' hModel hModel' sectionRestrict sectionRestrict_spec
      IsIso
        (AlgebraicGeometry.projMapThetaOnTarget sectionRestrict
          (PcalA'.actualTwist n) (PcalA.actualTwist n)
          (AlgebraicGeometry.projMap PcalA' PcalA sectionRestrict).map
          ((AlgebraicGeometry.projMap PcalA' PcalA sectionRestrict).theta n) hTop
          (AlgebraicGeometry.projMapDomainTopInclusion_comp_ι sectionRestrict hTop)))


/- Lemma 27.15.2 (3): for nested affine opens, the transported theta family between compatible
section-ring models preserves the multiplication maps on all integral twists. -/
@[stacks 01NO] #check
  (AlgebraicGeometry.AffineOpenSectionProj.theta_mul :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U U' : S.affineOpens}
      {A A' sigma tau : Type u}
      [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
      [CommRing A'] [SetLike tau A'] [AddSubgroupClass tau A']
      (calA : ℕ → sigma) [GradedRing calA]
      (calA' : ℕ → tau) [GradedRing calA']
      (h : (U : S.Opens) ≤ (U' : S.Opens))
      (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf)
      [𝒜.IsCommutative]
      (hqc : 𝒜.IsQuasicoherent)
      (model : ∀ d : ℕ,
        (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ calA d)
      (model' : ∀ d : ℕ,
        (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U' : S.Opens)) ≃+ calA' d)
      (hModel : AlgebraicGeometry.AffineOpenSectionProj.IsAffineOpenSectionModel
        calA 𝒜 U model)
      (hModel' : AlgebraicGeometry.AffineOpenSectionProj.IsAffineOpenSectionModel
        calA' 𝒜 U' model')
      (PcalA : AlgebraicGeometry.ProjTwistPresentation calA)
      (PcalA' : AlgebraicGeometry.ProjTwistPresentation calA')
      (sectionRestrict : calA' →+*ᵍ calA)
      (sectionRestrict_spec :
        ∀ d : ℕ, ∀ x : calA' d,
          model d
              ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom)
                ((model' d).symm x)) =
            (sectionRestrict.gradedAddHom d) x),
      let hTop := AlgebraicGeometry.AffineOpenSectionProj.domain_eq_top
        calA calA' h 𝒜 hqc model model' hModel hModel' sectionRestrict sectionRestrict_spec
      AlgebraicGeometry.ProjMap.ThetaOnTargetMulCompatible PcalA' PcalA
        (AlgebraicGeometry.projMapOnTarget sectionRestrict
          (AlgebraicGeometry.projMap PcalA' PcalA sectionRestrict).map hTop)
        (fun n ↦ AlgebraicGeometry.projMapThetaOnTarget sectionRestrict
          (PcalA'.actualTwist n) (PcalA.actualTwist n)
          (AlgebraicGeometry.projMap PcalA' PcalA sectionRestrict).map
          ((AlgebraicGeometry.projMap PcalA' PcalA sectionRestrict).theta n) hTop
          (AlgebraicGeometry.projMapDomainTopInclusion_comp_ι sectionRestrict hTop)))
