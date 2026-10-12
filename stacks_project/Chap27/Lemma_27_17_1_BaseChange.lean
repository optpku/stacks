/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap27.Lemma_27_16_10
public import stacks_project.Chap27.Lemma_27_17_1_AssociatedSheaf

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
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

/-- Explicit associated-module base-change data over a verified relative-`Proj` presentation. -/
structure AssociatedBaseChangeComparison
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation)
    {S' : Scheme.{u}} (g : S' ⟶ S)
    (relativePresentation : Scheme.Hom.RelativeProjPresentation π)
    (baseChange : Scheme.Hom.RelativeProjBaseChange relativePresentation g) where
  /-- The generic presentation uses the original graded algebra `calA`. -/
  algebra_eq : relativePresentation.algebra = calA
  /-- The generic presentation uses the twists of the Section 27.15 presentation. -/
  twist_eq : ∀ n : ℤ, relativePresentation.twist n = presentation.twistAlgebra n
  /-- Pullback of graded modules along `g`. -/
  gradedBaseChange : Modules calA ⥤
    (GradedModuleSheaf.isQuasicoherent baseChange.presentation.algebra).FullSubcategory
  /-- Degreewise, graded base change is pullback of the original module sheaf. -/
  gradedBaseChange_obj : ∀ (M : Modules calA) (n : ℤ),
    (gradedBaseChange.obj M).obj n ≅ (Scheme.Modules.pullback g).obj (M.obj n)
  /-- The associated-module functor after relative-`Proj` base change. -/
  baseChangedAssociated :
    (GradedModuleSheaf.isQuasicoherent baseChange.presentation.algebra).FullSubcategory ⥤
      (pullback π g).Modules
  /-- The canonical natural isomorphism comparing association before and after base change. -/
  iso : construction.functor ⋙ Scheme.Modules.pullback (pullback.fst π g) ≅
    gradedBaseChange ⋙ baseChangedAssociated

namespace AssociatedBaseChangeComparison

/-- Construct associated base-change data from explicit functors, specifications, and an iso. -/
def of
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    (construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation)
    {S' : Scheme.{u}} (g : S' ⟶ S)
    (relativePresentation : Scheme.Hom.RelativeProjPresentation π)
    (baseChange : Scheme.Hom.RelativeProjBaseChange relativePresentation g)
    (algebra_eq : relativePresentation.algebra = calA)
    (twist_eq : ∀ n : ℤ, relativePresentation.twist n = presentation.twistAlgebra n)
    (gradedBaseChange : Modules calA ⥤
      (GradedModuleSheaf.isQuasicoherent baseChange.presentation.algebra).FullSubcategory)
    (gradedBaseChange_obj : ∀ (M : Modules calA) (n : ℤ),
      (gradedBaseChange.obj M).obj n ≅ (Scheme.Modules.pullback g).obj (M.obj n))
    (baseChangedAssociated :
      (GradedModuleSheaf.isQuasicoherent baseChange.presentation.algebra).FullSubcategory ⥤
        (pullback π g).Modules)
    (iso : construction.functor ⋙ Scheme.Modules.pullback (pullback.fst π g) ≅
      gradedBaseChange ⋙ baseChangedAssociated) :
    AssociatedBaseChangeComparison calA hqc A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionRestrict_spec sectionProjDomainTop sectionDegreeZeroIso π
      construction g relativePresentation baseChange where
  algebra_eq := algebra_eq
  twist_eq := twist_eq
  gradedBaseChange := gradedBaseChange
  gradedBaseChange_obj := gradedBaseChange_obj
  baseChangedAssociated := baseChangedAssociated
  iso := iso

end AssociatedBaseChangeComparison

/-- Formation of the associated module commutes with the explicit relative-`Proj` base change. -/
def associatedBaseChangeIso
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    {construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation}
    {S' : Scheme.{u}} {g : S' ⟶ S}
    {relativePresentation : Scheme.Hom.RelativeProjPresentation π}
    {baseChange : Scheme.Hom.RelativeProjBaseChange relativePresentation g}
    (comparison : AssociatedBaseChangeComparison calA hqc A σ sectionGrading P
      sectionGradingIso sectionRestrict sectionRestrict_spec sectionProjDomainTop
      sectionDegreeZeroIso π construction g relativePresentation baseChange) :
    construction.functor ⋙ Scheme.Modules.pullback (pullback.fst π g) ≅
      comparison.gradedBaseChange ⋙ comparison.baseChangedAssociated :=
  comparison.iso

/-- The degreewise pullback specification of explicit graded base-change data. -/
def gradedBaseChange_obj
    {presentation : RelativeProjTwistPresentation calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π}
    {construction : AssociatedModuleFunctor calA A σ sectionGrading P sectionGradingIso
      sectionRestrict sectionProjDomainTop sectionDegreeZeroIso π hqc sectionRestrict_spec
      presentation}
    {S' : Scheme.{u}} {g : S' ⟶ S}
    {relativePresentation : Scheme.Hom.RelativeProjPresentation π}
    {baseChange : Scheme.Hom.RelativeProjBaseChange relativePresentation g}
    (comparison : AssociatedBaseChangeComparison calA hqc A σ sectionGrading P
      sectionGradingIso sectionRestrict sectionRestrict_spec sectionProjDomainTop
      sectionDegreeZeroIso π construction g relativePresentation baseChange)
    (M : Modules calA) (n : ℤ) :
    (comparison.gradedBaseChange.obj M).obj n ≅
      (Scheme.Modules.pullback g).obj (M.obj n) :=
  comparison.gradedBaseChange_obj M n

end

end AlgebraicGeometry.RelativeProjTwistPresentation
