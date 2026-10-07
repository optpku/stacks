module

public import stacks_project.Chap27.Lemma_27_17_1_AssociatedSheaf

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped MonoidalCategory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeProjTwistPresentation

section

variable {S X : Scheme.{u}}
variable (calA : GradedAlgebraSheaf.{u, u} S.sheaf)
variable (hqc : ∀ n : ℤ, (calA n).IsQuasicoherent)
variable (A : S.affineOpens → Type u) (σ : S.affineOpens → Type u)
variable [∀ U, CommRing (A U)] [∀ U, SetLike (σ U) (A U)]
variable [∀ U, AddSubgroupClass (σ U) (A U)]
variable (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
variable [∀ U, GradedRing (sectionGrading U)]
variable (P : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
variable (sectionGradingIso : ∀ (U : S.affineOpens) (d : ℕ),
  (calA (Int.ofNat d)).val.obj (Opposite.op (U : S.Opens)) ≃ sectionGrading U d)
variable (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
  (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
variable (sectionRestrict_spec :
  ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens)),
    ∀ d : ℕ, ∀ x : sectionGrading U' d,
      sectionGradingIso U d
          ((((calA (Int.ofNat d)).val.map (homOfLE h).op).hom)
            ((sectionGradingIso U' d).symm x)) =
        (sectionRestrict h).gradedAddHom d x)
variable (sectionProjDomainTop : ∀ ⦃U U' : S.affineOpens⦄
  (h : (U : S.Opens) ≤ (U' : S.Opens)), projMapDomain (sectionRestrict h) = ⊤)
variable (sectionDegreeZeroIso : ∀ U : S.affineOpens,
  sectionGrading U 0 ≃+* S.presheaf.obj (Opposite.op (U : S.Opens)))
variable (π : X ⟶ S)

/-- Explicit tensor-product and tensor-comparison data for an associated-module construction. -/
structure AssociatedTensorComparison
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation) where
  /-- The actual graded tensor-product bifunctor over `calA`. -/
  gradedTensor : Modules calA ⥤ Modules calA ⥤ Modules calA
  /-- The canonical map `M̃ ⊗ Ñ ⟶ (M ⊗_calA N)̃`. -/
  hom : ∀ M N : Modules calA,
    construction.functor.obj M ⊗ construction.functor.obj N ⟶
      construction.functor.obj ((gradedTensor.obj M).obj N)
  /-- The tensor comparisons are natural in both graded modules. -/
  naturality : ∀ {M M' N N' : Modules calA} (f : M ⟶ M') (g : N ⟶ N'),
    (construction.functor.map f ⊗ₘ construction.functor.map g) ≫ hom M' N' =
      hom M N ≫ construction.functor.map
        ((gradedTensor.map f).app N ≫ (gradedTensor.obj M').map g)

namespace AssociatedTensorComparison

/-- Construct tensor-comparison data from an explicit bifunctor, comparison maps, and naturality. -/
def of
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation)
    (gradedTensor : Modules calA ⥤ Modules calA ⥤ Modules calA)
    (hom : ∀ M N : Modules calA,
      construction.functor.obj M ⊗ construction.functor.obj N ⟶
        construction.functor.obj ((gradedTensor.obj M).obj N))
    (naturality : ∀ {M M' N N' : Modules calA} (f : M ⟶ M') (g : N ⟶ N'),
      (construction.functor.map f ⊗ₘ construction.functor.map g) ≫ hom M' N' =
        hom M N ≫ construction.functor.map
          ((gradedTensor.map f).app N ≫ (gradedTensor.obj M').map g)) :
    AssociatedTensorComparison calA hqc A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π
      construction where
  gradedTensor := gradedTensor
  hom := hom
  naturality := naturality

end AssociatedTensorComparison

/-- The graded tensor bifunctor carried by explicit tensor-comparison data. -/
def gradedTensor
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    {construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation}
    (comparison : AssociatedTensorComparison calA hqc A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π
      construction) : Modules calA ⥤ Modules calA ⥤ Modules calA :=
  comparison.gradedTensor

/-- The component `M̃ ⊗ Ñ ⟶ (M ⊗_calA N)̃` of the tensor comparison. -/
def associatedTensor
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    {construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation}
    (comparison : AssociatedTensorComparison calA hqc A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π
      construction) (M N : Modules calA) :
    construction.functor.obj M ⊗ construction.functor.obj N ⟶
      construction.functor.obj ((comparison.gradedTensor.obj M).obj N) :=
  comparison.hom M N

/-- The associated tensor comparison is natural in both arguments. -/
theorem associatedTensor_naturality
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    {construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation}
    (comparison : AssociatedTensorComparison calA hqc A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π
      construction)
    {M M' N N' : Modules calA} (f : M ⟶ M') (g : N ⟶ N') :
    (construction.functor.map f ⊗ₘ construction.functor.map g) ≫
        associatedTensor calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
          sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π comparison M' N' =
      associatedTensor calA hqc A σ sectionGrading P sectionGradingIso sectionRestrict
          sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π comparison M N ≫
        construction.functor.map ((comparison.gradedTensor.map f).app N ≫
          (comparison.gradedTensor.obj M').map g) := sorry

end

end AlgebraicGeometry.RelativeProjTwistPresentation
