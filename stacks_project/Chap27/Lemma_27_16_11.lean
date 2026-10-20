/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.One
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.DegreeOneTwists
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry

section SourceCheck

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
variable (R : Scheme.RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel P
  sectionRestrict sectionRestrict_spec)
variable (F₁ : Scheme.RelativeProjDegreeFunctor S 𝒜 1)
variable (hF₁ : F₁.IsAssociatedToQuadruples)
variable (hgenerated : ∀ U : S.affineOpens,
  GradedAlgebra.GeneratedBy (sectionGrading U) 1)
variable (presentation : Scheme.RelativeProjTwist.Presentation
  𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv) R.toBase)

/- Lemma 27.16.11: an equipped relative projective spectrum of an affine-locally
degree-one-generated graded algebra represents the degree-one functor of invertible-module
quadruples modulo strict equivalence. -/
@[stacks 01O4] #check
  (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor.exists_isRepresentedBy_of_generatedByDegreeOne
    𝒜 hqc A σ sectionGrading model hModel P sectionRestrict sectionRestrict_spec
      R F₁ hF₁ hgenerated :
    ∃ x : F₁.toFunctor.obj (Opposite.op R.Y),
      F₁.toFunctor.IsRepresentedBy x ∧
        F₁.baseMap.app (Opposite.op R.Y) x = R.toBase)

/- Every integral twist on this relative projective spectrum is invertible. -/
#check
  (AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation.twist_invertible_of_generatedByDegreeOne
    𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv)
      presentation hgenerated :
    ∀ n : ℤ, Scheme.Modules.Invertible (presentation.twistAlgebra n))

/- The canonical multiplication morphism between any two integral twists is an isomorphism. -/
#check
  (AlgebraicGeometry.Scheme.RelativeProjTwist.Presentation.mulHom_isIso_of_generatedByDegreeOne
    𝒜 A σ sectionGrading P (fun U d ↦ (model U d).toEquiv)
      presentation hgenerated :
    ∀ a b : ℤ,
      IsIso (GradedAlgebraSheaf.mulHom presentation.twistAlgebra a b))

end SourceCheck

end AlgebraicGeometry
