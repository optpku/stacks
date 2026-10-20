module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeProjFromSections
import StacksCheckRecall

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
variable [F : RelativeProjFunctor S 𝒜]
variable (associatedToQuadruples : ∀ d : {n : ℕ // 1 ≤ n},
  (F.degreeFunctor d).IsAssociatedToQuadruples)
variable (representedPoint : F.toFunctor.obj (op (Scheme.relativeProj R)))
variable (representedPoint_isUniversal : F.toFunctor.IsRepresentedBy representedPoint)

/- Lemma 27.19.1: a multiplicative graded map into the integral powers of an invertible module
determines a unique canonical open-domain morphism to relative projective spectrum and a
compatible graded twist map; its degreewise squares commute, its restrictions agree with the
associated fixed-degree construction whenever the restricted degree is epimorphic, and on every
affine base chart it agrees with the canonical absolute projective section map. -/
@[stacks 01O9] #check
  (AlgebraicGeometry.Scheme.Modules.existsUnique_relativeProjSectionMap
      𝒜 hqc A σ sectionGrading model hModel P sectionRestrict sectionRestrict_spec
      R presentation f L ψ associatedToQuadruples representedPoint
      representedPoint_isUniversal :
    ∃! c : RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec R presentation f L ψ,
      RelativeProjSectionMap.IsCanonical (𝒜 := 𝒜)
        (associatedToQuadruples := associatedToQuadruples)
        (representedPoint := representedPoint) (c := c))

end

end AlgebraicGeometry.Scheme.Modules
