module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeProjFromSections

/-!
# Relative projective section maps on the full source

This file transports a relative projective section map from its natural open domain to the full
source scheme when that domain is top.
-/

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section

variable {S : Scheme.{u}}
variable (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [𝒜.IsCommutative]
variable (hqc : 𝒜.IsQuasicoherent)
variable (A σ : S.affineOpens → Type u)
variable [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
variable [∀ U, AddSubgroupClass (σ U) (A U)]
variable (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
variable [∀ U, GradedRing (sectionGrading U)]
variable (model : ∀ (U : S.affineOpens) (d : ℕ),
  (𝒜 (Int.ofNat d)).val.obj (op (U : S.Opens)) ≃+ sectionGrading U d)
variable (hModel : ∀ U : S.affineOpens,
  AffineOpenSectionProj.IsAffineOpenSectionModel (sectionGrading U) 𝒜 U (model U))
variable (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
variable (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
  (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
variable (sectionRestrict_spec :
  ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
    (d : ℕ) (x : sectionGrading U' d),
    model U d
        ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom) ((model U' d).symm x)) =
      (sectionRestrict h).gradedAddHom d x)
variable (R : Scheme.RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel P
  sectionRestrict sectionRestrict_spec)
variable (presentation : Scheme.RelativeProjTwist.Presentation 𝒜 A σ sectionGrading P
  (fun U d ↦ (model U d).toEquiv) (Scheme.relativeProjπ R))
variable {T : Scheme.{u}} (f : T ⟶ S) (L : T.Modules) [Invertible L]
variable (ψ : Scheme.RelativeProjTwist.Hom 𝒜 f
  (@RingedSpace.InvertiblePower.gradedAlgebra _ L
    (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L))))

namespace RelativeProjSectionMap

/-- The canonical morphism from the full source scheme to the natural domain of a relative
projective section map when that domain is top. -/
abbrev domainTopInclusion
    (c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ)
    (hTop : c.domain = ⊤) :
    T ⟶ c.domain.toScheme :=
  (Scheme.topIso T).inv ≫ (T.isoOfEq hTop.symm).hom

/-- The canonical morphism from the full source scheme to a top natural domain is inverse to
the domain inclusion. -/
theorem domainTopInclusion_comp_ι
    (c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ)
    (hTop : c.domain = ⊤) :
    domainTopInclusion 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ c hTop ≫ c.domain.ι = 𝟙 T := sorry

/-- A relative projective section map extends from its natural domain to the full source scheme
when that domain is top. -/
abbrev mapOnSource
    (c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ)
    (hTop : c.domain = ⊤) :
    T ⟶ Scheme.relativeProj R :=
  domainTopInclusion 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
    sectionRestrict_spec R presentation f L ψ c hTop ≫ c.map

/-- The full-source relative projective section map commutes with the structure morphisms to
the base. -/
theorem mapOnSource_over_base
    (c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ)
    (hTop : c.domain = ⊤) :
    mapOnSource 𝒜 hqc A σ sectionGrading model hModel P sectionRestrict
      sectionRestrict_spec R presentation f L ψ c hTop ≫ Scheme.relativeProjπ R = f := sorry

end RelativeProjSectionMap

end

end AlgebraicGeometry.Scheme.Modules
