module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.DegreeOpen
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Affine
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Realization
public import ReasLib.RingTheory.GradedAlgebra.GeneratedBy

/-!
# Degree-one relative projective functors

An equipped relative projective spectrum of an algebra generated in degree one represents the
degree-one functor associated with invertible-module quadruples.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor

/-- An equipped relative projective spectrum of an affine-locally degree-one-generated graded
algebra carries a universal point of its associated degree-one functor over the given base
scheme. -/
theorem exists_isRepresentedBy_of_generatedByDegreeOne
    {S : Scheme.{u}}
    (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [𝒜.IsCommutative]
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
          (sectionRestrict h).gradedAddHom d x)
    (R : Scheme.RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel P
      sectionRestrict sectionRestrict_spec)
    (F₁ : Scheme.RelativeProjDegreeFunctor S 𝒜 1)
    (hF₁ : F₁.IsAssociatedToQuadruples)
    (hgenerated : ∀ U : S.affineOpens,
      GradedAlgebra.GeneratedBy (sectionGrading U) 1) :
    ∃ x : F₁.toFunctor.obj (Opposite.op R.Y),
      F₁.toFunctor.IsRepresentedBy x ∧
        F₁.baseMap.app (Opposite.op R.Y) x = R.toBase := sorry

end AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor
