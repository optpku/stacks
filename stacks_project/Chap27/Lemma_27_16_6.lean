module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Representability
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Functor
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
variable (R : (Scheme.relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
  sectionRestrict sectionRestrict_spec).Realization)

/- Lemma 27.16.6 (`01NZ`): the relative projective scheme obtained from the affine-open gluing
is isomorphic over `S` to the chosen scheme representing the relative projective functor. -/
@[stacks 01NZ] #check
  (RelativeProjFunctor.nonempty_iso_over_of_realization_and_isRepresentedBy
      𝒜 hqc A σ sectionGrading model hModel P sectionRestrict sectionRestrict_spec
      baseMap degreeToFunctor_base associatedToQuadruples R
      F.toFunctor.reprx IsRepresentedBy.of_isRepresentable :
    Nonempty
      (Over.mk R.toBase ≅
        Over.mk
          (baseMap.app (Opposite.op F.toFunctor.reprX) F.toFunctor.reprx)))

end

end AlgebraicGeometry
