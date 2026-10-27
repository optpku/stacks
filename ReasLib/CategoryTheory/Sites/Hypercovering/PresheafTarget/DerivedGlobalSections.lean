/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Restriction
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.DerivedDescent

/-!
# Derived global-sections comparison for a hypercovering

If `K` is a hypercovering of the terminal presheaf, global sections on the total
site identify with global sections after `a_*`, and this identification transports
to unbounded derived global sections. The canonical comparison
`RΓ(C, -) ⟶ a⁻¹ ⋙ RΓ((C / K)_total, -)` is the derived unit of `a⁻¹ ⊣ Ra_*`
followed by that Leray identification.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite Functor ComplexShape
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [h_eq : HasEqualizers C] [h_pb : HasPullbacks C]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{w} J)
variable [HasSheafify J AddCommGrpCat.{max w u v}]
variable [HasSheafify (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}]
variable [HasGlobalSectionsFunctor J AddCommGrpCat.{max w u v}]
variable [HasGlobalSectionsFunctor (overSiteTotalTopology J K.simplicial)
    AddCommGrpCat.{max w u v}]
variable [(RightDerived.Cochain.toDerived
    (Sheaf.Γ J AddCommGrpCat.{max w u v})).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf J AddCommGrpCat.{max w u v}) (up ℤ))]
variable [(RightDerived.Cochain.toDerived
    (Sheaf.Γ (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v})).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso
      (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) (up ℤ))]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]

/-- Underived identification `Γ((C / K)_total, -) ≅ Γ(C, a_* -)`. -/
@[expose] def directImageCompGlobalSectionsIso :
    directImage J K.simplicial AddCommGrpCat.{max w u v} ⋙
      Sheaf.Γ J AddCommGrpCat.{max w u v} ≅
    Sheaf.Γ (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v} :=
  (((constantSheafΓAdj J AddCommGrpCat.{max w u v}).comp
        (sheafLocalizationAdjunction J K AddCommGrpCat.{max w u v})).ofNatIsoLeft
      ((totalForget K.simplicial).constantSheafRestrictionIso
        (overSiteTotalTopology J K.simplicial) J AddCommGrpCat.{max w u v})).rightAdjointUniq
    (constantSheafΓAdj (overSiteTotalTopology J K.simplicial)
      AddCommGrpCat.{max w u v})

/-- Cochain-level reassociation `(a_* ⋙ Γ_C).mapHC ⋙ Q ≅ a_*.mapHC ⋙ (Γ_C.mapHC ⋙ Q)`. -/
private def rGammaDirectImageToIteratedIso :
    RightDerived.Cochain.toDerived
        (directImage J K.simplicial AddCommGrpCat.{max w u v} ⋙
          Sheaf.Γ J AddCommGrpCat.{max w u v}) ≅
      (directImage J K.simplicial AddCommGrpCat.{max w u v}).mapHomologicalComplex (up ℤ) ⋙
        RightDerived.Cochain.toDerived (Sheaf.Γ J AddCommGrpCat.{max w u v}) :=
  isoWhiskerRight
      (mapHomologicalComplexCompIso
        (Iso.refl
          (directImage J K.simplicial AddCommGrpCat.{max w u v} ⋙
            Sheaf.Γ J AddCommGrpCat.{max w u v}))
        (up ℤ)).symm
      (DerivedCategory.Q : CochainComplex AddCommGrpCat.{max w u v} ℤ ⥤
        DerivedCategory AddCommGrpCat.{max w u v}) ≪≫
    associator
      ((directImage J K.simplicial AddCommGrpCat.{max w u v}).mapHomologicalComplex (up ℤ))
      ((Sheaf.Γ J AddCommGrpCat.{max w u v}).mapHomologicalComplex (up ℤ))
      (DerivedCategory.Q : CochainComplex AddCommGrpCat.{max w u v} ℤ ⥤
        DerivedCategory AddCommGrpCat.{max w u v})

/-- Iterated cochain unit of `Ra_* ⋙ RΓ(C, -)` as a right-derived model of `a_* ⋙ Γ(C, -)`. -/
def rGammaDirectImageUnit :
    RightDerived.Cochain.toDerived
        (directImage J K.simplicial AddCommGrpCat.{max w u v} ⋙
          Sheaf.Γ J AddCommGrpCat.{max w u v}) ⟶
      (DerivedCategory.Q :
          CochainComplex
              (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) ℤ ⥤
            DerivedCategory
              (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v})) ⋙
        (directImageDerived J K ⋙
          RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v})) :=
  (rGammaDirectImageToIteratedIso J K).hom ≫
    RightDerived.Composition.iteratedUnit
      (RightDerived.KInjective.unit
        (directImage J K.simplicial AddCommGrpCat.{max w u v}))
      (RightDerived.Cochain.unit (Sheaf.Γ J AddCommGrpCat.{max w u v}))

/-- The iterated model `Ra_* ⋙ RΓ(C, -)` is a right-derived functor of `a_* ⋙ Γ(C, -)`. -/
instance rGammaDirectImage_isRightDerived :
    (directImageDerived J K ⋙
        RightDerived.Cochain.functor
          (Sheaf.Γ J AddCommGrpCat.{max w u v})).IsRightDerivedFunctor
      (rGammaDirectImageUnit J K)
      (HomologicalComplex.quasiIso
        (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v})
        (up ℤ)) := sorry

/-- Leray identification `Ra_* ⋙ RΓ(C, -) ≅ RΓ((C / K)_total, -)`. -/
@[expose] def rGammaDirectImageIso :
    directImageDerived J K ⋙
      RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v}) ≅
    RightDerived.Cochain.functor
      (Sheaf.Γ (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) :=
  RightDerived.natIsoOfIso
    (DerivedCategory.Q :
      CochainComplex
          (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) ℤ ⥤
        DerivedCategory
          (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}))
    (HomologicalComplex.quasiIso
      (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v})
      (up ℤ))
    (rGammaDirectImageUnit J K)
    (RightDerived.Cochain.unit
      (Sheaf.Γ (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}))
    (isoWhiskerRight
      (NatIso.mapHomologicalComplex (directImageCompGlobalSectionsIso J K) (up ℤ))
      (DerivedCategory.Q : CochainComplex AddCommGrpCat.{max w u v} ℤ ⥤
        DerivedCategory AddCommGrpCat.{max w u v}))

/-- Canonical comparison `RΓ(C, -) ⟶ a⁻¹ ⋙ RΓ((C / K)_total, -)`. -/
@[expose] def rGammaInverseImageComparison :
    RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v}) ⟶
      inverseImageDerived J K ⋙
        RightDerived.Cochain.functor
          (Sheaf.Γ (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) :=
  whiskerRight (derivedUnit J K)
      (RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v})) ≫
    (associator (inverseImageDerived J K) (directImageDerived J K)
        (RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v}))).hom ≫
    whiskerLeft (inverseImageDerived J K) (rGammaDirectImageIso J K).hom

/-- The inverse-image comparison is the derived adjunction unit, reassociated and
postcomposed with the Leray identification. -/
theorem rGammaInverseImageComparison_eq :
    rGammaInverseImageComparison J K =
      whiskerRight (derivedUnit J K)
          (RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v})) ≫
        (associator (inverseImageDerived J K) (directImageDerived J K)
            (RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v}))).hom ≫
        whiskerLeft (inverseImageDerived J K) (rGammaDirectImageIso J K).hom := sorry

/-- At `E`, the inverse-image comparison is `RΓ` of the derived unit followed by
the Leray identification at `a⁻¹ E`. -/
theorem rGammaInverseImageComparison_app
    (E : DerivedCategory (Sheaf J AddCommGrpCat.{max w u v})) :
    (rGammaInverseImageComparison J K).app E =
      (RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v})).map
          ((derivedUnit J K).app E) ≫
        (rGammaDirectImageIso J K).hom.app ((inverseImageDerived J K).obj E) := sorry

/-- The canonical inverse-image comparison is invertible at every object of the
unbounded derived category of abelian sheaves. -/
instance rGammaInverseImageComparison_app_isIso
    (E : DerivedCategory (Sheaf J AddCommGrpCat.{max w u v})) :
    IsIso ((rGammaInverseImageComparison J K).app E) := sorry

/-- The comparison `RΓ(C, -) ⟶ a⁻¹ ⋙ RΓ((C / K)_total, -)` is an isomorphism of functors. -/
instance rGammaInverseImageComparison_isIso :
    IsIso (rGammaInverseImageComparison J K) := sorry

end CategoryTheory.SemiRepresentableFamily
