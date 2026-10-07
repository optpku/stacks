module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.AffineOpenComposition
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Basis.Basic

/-!
# Realizations of relative projective spectra

This module constructs basis-indexed scheme gluing data from compatible projective spectra of
graded section-ring models on affine opens.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The basis-indexed gluing datum whose local scheme over an affine open `U` is the projective
spectrum of a compatible graded-ring model for the nonnegative sections of `𝒜` on `U`. -/
noncomputable def relativeProjGluingData
    {S : Scheme.{u}}
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf ℤ)
    [𝒜.IsCommutative]
    (hqc : 𝒜.IsQuasicoherent)
    (A σ : S.affineOpens → Type u)
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
    [∀ U, GradedRing (sectionGrading U)]
    (model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d)
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U))
    (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
    (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
      (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
    (sectionRestrict_spec :
      ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
        (d : ℕ) (x : sectionGrading U' d),
        model U d
            ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom)
              ((model U' d).symm x)) =
          (sectionRestrict h).gradedAddHom d x) :
    BasisSchemeGluing S where
  ι := S.affineOpens
  U U := U
  isBasis := by
    rw [Subtype.range_coe]
    exact S.isBasis_affineOpens
  X U := Proj (sectionGrading U)
  f U := AffineOpenSectionProj.toAffineOpen
    (sectionGrading U) 𝒜 U (model U) (hModel U)
  rho {U U'} h :=
    let hTop := AffineOpenSectionProj.domain_eq_top
      (sectionGrading U) (sectionGrading U') h 𝒜 hqc
      (model U) (model U') (hModel U) (hModel U')
      (sectionRestrict h) (sectionRestrict_spec h)
    projMapOnTarget (sectionRestrict h)
      (projMap (P U') (P U) (sectionRestrict h)).map hTop
  isPullback_rho {U U'} h :=
    AffineOpenSectionProj.isPullback
      (sectionGrading U) (sectionGrading U') h 𝒜 hqc
      (model U) (model U') (hModel U) (hModel U')
      (P U) (P U') (sectionRestrict h) (sectionRestrict_spec h)
  cocycle {U U' U''} h h' :=
    let hTop := AffineOpenSectionProj.domain_eq_top
      (sectionGrading U) (sectionGrading U') h 𝒜 hqc
      (model U) (model U') (hModel U) (hModel U')
      (sectionRestrict h) (sectionRestrict_spec h)
    let hTop' := AffineOpenSectionProj.domain_eq_top
      (sectionGrading U') (sectionGrading U'') h' 𝒜 hqc
      (model U') (model U'') (hModel U') (hModel U'')
      (sectionRestrict h') (sectionRestrict_spec h')
    let hTopComp := AffineOpenSectionProj.domain_eq_top
      (sectionGrading U) (sectionGrading U'') (h.trans h') 𝒜 hqc
      (model U) (model U'') (hModel U) (hModel U'')
      (sectionRestrict (h.trans h')) (sectionRestrict_spec (h.trans h'))
    affineOpenSectionProj_map_comp
      (sectionGrading U) (sectionGrading U') (sectionGrading U'')
      (P U) (P U') (P U'') 𝒜 hqc h h'
      (fun d ↦ (model U d).toEquiv)
      (fun d ↦ (model U' d).toEquiv)
      (fun d ↦ (model U'' d).toEquiv)
      (sectionRestrict h) (sectionRestrict_spec h)
      (sectionRestrict h') (sectionRestrict_spec h')
      (sectionRestrict (h.trans h')) (sectionRestrict_spec (h.trans h'))
      hTop hTop' hTopComp

/-- An equipped relative-projective-spectrum realization consists of a scheme over the base,
its structure morphism, and compatible identifications with the affine projective models. -/
abbrev RelativeProjRealization
    {S : Scheme.{u}}
    (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf ℤ)
    [𝒜.IsCommutative]
    (hqc : 𝒜.IsQuasicoherent)
    (A σ : S.affineOpens → Type u)
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
    [∀ U, GradedRing (sectionGrading U)]
    (model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d)
    (hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U))
    (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
    (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
      (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
    (sectionRestrict_spec :
      ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
        (d : ℕ) (x : sectionGrading U' d),
        model U d
            ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom)
              ((model U' d).symm x)) =
          (sectionRestrict h).gradedAddHom d x) :=
  (relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
    sectionRestrict sectionRestrict_spec).Realization

/-- The scheme underlying an equipped relative-projective-spectrum realization. -/
abbrev relativeProj
    {S : Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf ℤ}
    [𝒜.IsCommutative]
    {hqc : 𝒜.IsQuasicoherent}
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}
    {hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U)}
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    {sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
      (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U}
    {sectionRestrict_spec :
      ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
        (d : ℕ) (x : sectionGrading U' d),
        model U d
            ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom)
              ((model U' d).symm x)) =
          (sectionRestrict h).gradedAddHom d x}
    (R : RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec) : Scheme.{u} :=
  R.Y

/-- The structural morphism from an equipped relative projective spectrum to its base scheme. -/
abbrev relativeProjπ
    {S : Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf ℤ}
    [𝒜.IsCommutative]
    {hqc : 𝒜.IsQuasicoherent}
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}
    {hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U)}
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    {sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
      (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U}
    {sectionRestrict_spec :
      ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
        (d : ℕ) (x : sectionGrading U' d),
        model U d
            ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom)
              ((model U' d).symm x)) =
          (sectionRestrict h).gradedAddHom d x}
    (R : RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec) : relativeProj R ⟶ S :=
  R.toBase

namespace RelativeProjRealization

/-- Forgetting the chosen affine-local identifications gives the underlying realization
property for the structural morphism. -/
theorem realizes
    {S : Scheme.{u}}
    {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf ℤ}
    [𝒜.IsCommutative]
    {hqc : 𝒜.IsQuasicoherent}
    {A σ : S.affineOpens → Type u}
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    {sectionGrading : ∀ U : S.affineOpens, ℕ → σ U}
    [∀ U, GradedRing (sectionGrading U)]
    {model : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d}
    {hModel : ∀ U : S.affineOpens,
      AffineOpenSectionProj.IsAffineOpenSectionModel
        (sectionGrading U) 𝒜 U (model U)}
    {P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U)}
    {sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
      (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U}
    {sectionRestrict_spec :
      ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
        (d : ℕ) (x : sectionGrading U' d),
        model U d
            ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom)
              ((model U' d).symm x)) =
          (sectionRestrict h).gradedAddHom d x}
    (R : RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec) :
    (relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec).Realizes (relativeProjπ R) :=
  BasisSchemeGluing.Realization.realizes
    (relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec) R

end RelativeProjRealization

end AlgebraicGeometry.Scheme
