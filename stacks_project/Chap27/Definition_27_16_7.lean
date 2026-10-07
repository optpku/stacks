module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Representability
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry

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
  (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃+ sectionGrading U d)
variable (hModel : ∀ U : S.affineOpens,
  AffineOpenSectionProj.IsAffineOpenSectionModel
    (sectionGrading U) 𝒜 U (model U))
variable (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
variable (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
  (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
variable (sectionRestrict_spec :
  ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
    (d : ℕ) (x : sectionGrading U' d),
    model U d
        ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom)
          ((model U' d).symm x)) =
      (sectionRestrict h).gradedAddHom d x)
variable [F : RelativeProjFunctor S 𝒜]
variable (baseMap : F.toFunctor ⟶ yoneda.obj S)
variable (degreeToFunctor_base : ∀ d : { n : ℕ // 1 ≤ n },
  F.degreeToFunctor d ≫ baseMap = (F.degreeFunctor d).baseMap)
variable (associatedToQuadruples : ∀ d : { n : ℕ // 1 ≤ n },
  (F.degreeFunctor d).IsAssociatedToQuadruples)
variable (R : Scheme.RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel P
  sectionRestrict sectionRestrict_spec)

/- Definition 27.16.7

The relative homogeneous spectrum of `𝒜` over `S` is the scheme in an equipped realization of
the affine projective gluing datum, with its structural morphism to `S`. -/
@[stacks 01O0] #check (AlgebraicGeometry.Scheme.relativeProjπ R :
  AlgebraicGeometry.Scheme.relativeProj R ⟶ S)

/- Under the affine-model and degree-chart compatibility hypotheses, the equipped relative
projective spectrum carries a universal point whose image is its structural morphism. -/
#check
  (AlgebraicGeometry.RelativeProjFunctor.exists_isRepresentedBy_of_realization
      𝒜 hqc A σ sectionGrading model hModel P sectionRestrict sectionRestrict_spec
      baseMap degreeToFunctor_base associatedToQuadruples R :
    ∃ x : F.toFunctor.obj (Opposite.op (AlgebraicGeometry.Scheme.relativeProj R)),
      F.toFunctor.IsRepresentedBy x ∧
        baseMap.app (Opposite.op (AlgebraicGeometry.Scheme.relativeProj R)) x =
          AlgebraicGeometry.Scheme.relativeProjπ R)

end

end AlgebraicGeometry
