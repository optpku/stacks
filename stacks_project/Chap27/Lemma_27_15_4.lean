module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Realization

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

section

variable {S : Scheme.{u}}
variable (𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf ℤ)
variable [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
variable (A σ : S.affineOpens → Type u)
variable [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
variable [∀ U, AddSubgroupClass (σ U) (A U)]
variable (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
variable [∀ U, GradedRing (sectionGrading U)]
variable (model : ∀ (U : S.affineOpens) (d : ℕ),
  (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d)
variable (hModel : ∀ U : S.affineOpens,
  AffineOpenSectionProj.IsAffineOpenSectionModel (sectionGrading U) 𝒜 U (model U))
variable (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
variable (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
  (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
variable (sectionRestrict_spec :
  ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
    (d : ℕ) (x : sectionGrading U' d),
    model U d
        ((((𝒜 (Int.ofNat d)).val.map (CategoryTheory.homOfLE h).op).hom)
          ((model U' d).symm x)) =
      (sectionRestrict h).gradedAddHom d x)

/- Lemma 27.15.4: the affine-open projective spectra of compatible section-ring models have
an equipped realization over `S`, with the prescribed local identifications and transitions. -/
@[stacks 01NQ] #check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization.nonempty
      (AlgebraicGeometry.Scheme.relativeProjGluingData
        𝒜 hqc A σ sectionGrading model hModel P sectionRestrict sectionRestrict_spec) :
    Nonempty
      (AlgebraicGeometry.Scheme.relativeProjGluingData
        𝒜 hqc A σ sectionGrading model hModel P sectionRestrict sectionRestrict_spec).Realization)

end

end AlgebraicGeometry.Scheme
