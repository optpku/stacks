module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.TwistGluing

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Compatibility name for multiplication on the nonnegative pieces of an integral graded
algebra sheaf. -/
abbrev gradedAlgebraSheafNatMul
    {X : Scheme.{u}} (ℬ : GradedAlgebraSheaf.{u, u} X.sheaf)
    (U : X.Opens) (i j : ℕ) :
    Γ(ℬ (Int.ofNat i), U) → Γ(ℬ (Int.ofNat j), U) → Γ(ℬ (Int.ofNat (i + j)), U) :=
  Scheme.RelativeProjTwist.natMul ℬ U i j

/-- Compatibility name for a relative-projective integral twist algebra, its multiplicative
map, and its affine projective-spectrum comparisons. -/
abbrev RelativeProjTwistPresentation
    {S : Scheme.{u}}
    (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
    (A σ : S.affineOpens → Type u)
    [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
    [∀ U, AddSubgroupClass (σ U) (A U)]
    (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
    [∀ U, GradedRing (sectionGrading U)]
    (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
    (sectionGradingIso : ∀ (U : S.affineOpens) (d : ℕ),
      (𝒜 (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d)
    (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
      (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
    (sectionProjDomainTop : ∀ ⦃U U' : S.affineOpens⦄
      (h : (U : S.Opens) ≤ (U' : S.Opens)), projMapDomain (sectionRestrict h) = ⊤)
    (sectionDegreeZeroIso : ∀ U : S.affineOpens,
      sectionGrading U 0 ≃+* S.presheaf.obj (Opposite.op (U : S.Opens)))
    {X : Scheme.{u}} (π : X ⟶ S) : Type (u + 1) :=
  Scheme.RelativeProjTwist.Presentation
    𝒜 A σ sectionGrading P sectionGradingIso π

section SourceCheck

variable {S : Scheme.{u}}
variable (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf ℤ) [𝒜.IsCommutative]
variable (hqc : 𝒜.IsQuasicoherent)
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
        ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom) ((model U' d).symm x)) =
      (sectionRestrict h).gradedAddHom d x)

/- Lemma 27.15.5: an equipped realization of relative `Proj` carries a quasi-coherent integral
twist algebra, a multiplicative map from the nonnegative pieces of `𝒜`, affine comparisons
satisfying the section diagram, and the resulting map is uniquely determined by such comparisons.
-/
@[stacks 01NR] #check
  (Scheme.RelativeProjTwist.existsPresentation
    𝒜 hqc A σ sectionGrading model hModel P sectionRestrict sectionRestrict_spec :
    ∀ (R : (Scheme.relativeProjGluingData 𝒜 hqc A σ sectionGrading model hModel P
        sectionRestrict sectionRestrict_spec).Realization),
      ∃ presentation : Scheme.RelativeProjTwist.Presentation 𝒜 A σ sectionGrading P
          (fun U d ↦ (model U d).toEquiv) R.toBase,
        (∀ U : S.affineOpens, presentation.localSchemeIso U = R.localIso U) ∧
        ∀ (ψ' : Scheme.RelativeProjTwist.Hom
            𝒜 R.toBase presentation.twistAlgebra),
          Scheme.RelativeProjTwist.HomCompatibility 𝒜 A σ sectionGrading P
              (fun U d ↦ (model U d).toEquiv)
              R.toBase presentation.twistAlgebra presentation.localSchemeIso
                presentation.localTwistComparison ψ' →
            ψ' = presentation.psi)

end SourceCheck

end AlgebraicGeometry
