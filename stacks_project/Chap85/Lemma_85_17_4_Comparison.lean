/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
public import stacks_project.Chap85.Lemma_85_17_3_Adjunction

/-!
# Derived global-sections comparison for a hypercovering

If `K` is a hypercovering of the terminal presheaf, global sections on the total
site identify with global sections after `a_*`, and this identification transports
to unbounded derived global sections. The canonical comparison
`RΓ(C, -) ⟶ a⁻¹ ⋙ RΓ((C / K)_total, -)` is the derived unit of `a⁻¹ ⊣ Ra_*`
followed by that Leray identification.
-/

@[expose] public section

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

/-- Inverse image along `j_total` preserves constant abelian sheaves. -/
def constantSheafCompInverseImageIso :
    constantSheaf J AddCommGrpCat.{max w u v} ⋙
      inverseImage J K.simplicial AddCommGrpCat.{max w u v} ≅
    constantSheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v} :=
  (associator (const Cᵒᵖ)
      (presheafToSheaf J AddCommGrpCat.{max w u v})
      (inverseImage J K.simplicial AddCommGrpCat.{max w u v})).symm ≪≫
    isoWhiskerLeft (const Cᵒᵖ)
      ((totalForget K.simplicial).pushforwardContinuousSheafificationCompatibility
          AddCommGrpCat.{max w u v} (overSiteTotalTopology J K.simplicial) J).symm ≪≫
    associator (const Cᵒᵖ)
      ((whiskeringLeft _ _ AddCommGrpCat.{max w u v}).obj (totalForget K.simplicial).op)
      (presheafToSheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) ≪≫
    isoWhiskerRight
      (constCompWhiskeringLeftIso
        (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ
        (totalForget K.simplicial).op)
      (presheafToSheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v})

/-- Underived identification `Γ((C / K)_total, -) ≅ Γ(C, a_* -)`. -/
def directImageCompGlobalSectionsIso :
    directImage J K.simplicial AddCommGrpCat.{max w u v} ⋙
      Sheaf.Γ J AddCommGrpCat.{max w u v} ≅
    Sheaf.Γ (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v} :=
  (((constantSheafΓAdj J AddCommGrpCat.{max w u v}).comp
        (sheafLocalizationAdjunction J K AddCommGrpCat.{max w u v})).ofNatIsoLeft
      (constantSheafCompInverseImageIso J K)).rightAdjointUniq
    (constantSheafΓAdj (overSiteTotalTopology J K.simplicial)
      AddCommGrpCat.{max w u v})

/-- `directImageCompGlobalSectionsIso` is the right-adjoint uniqueness isomorphism of
`constantSheafΓAdj` after transporting `a⁻¹ ⊣ a_*` across constant sheaves. -/
theorem directImageCompGlobalSectionsIso_eq :
    directImageCompGlobalSectionsIso J K =
      (((constantSheafΓAdj J AddCommGrpCat.{max w u v}).comp
            (sheafLocalizationAdjunction J K AddCommGrpCat.{max w u v})).ofNatIsoLeft
          (constantSheafCompInverseImageIso J K)).rightAdjointUniq
        (constantSheafΓAdj (overSiteTotalTopology J K.simplicial)
          AddCommGrpCat.{max w u v}) :=
  sorry

/-- Cochain-level reassociation `(a_* ⋙ Γ_C).mapHC ⋙ Q ≅ a_*.mapHC ⋙ (Γ_C.mapHC ⋙ Q)`. -/
def rGammaDirectImageToIteratedIso :
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
        (up ℤ)) :=
  sorry

/-- Leray identification `Ra_* ⋙ RΓ(C, -) ≅ RΓ((C / K)_total, -)`. -/
def rGammaDirectImageIso :
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

/-- `rGammaDirectImageIso` is `RightDerived.natIsoOfIso` of `directImageCompGlobalSectionsIso`. -/
theorem rGammaDirectImageIso_eq :
    rGammaDirectImageIso J K =
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
            DerivedCategory AddCommGrpCat.{max w u v})) :=
  sorry

/-- Canonical comparison `RΓ(C, -) ⟶ a⁻¹ ⋙ RΓ((C / K)_total, -)`. -/
def rGammaInverseImageComparison :
    RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v}) ⟶
      inverseImageDerived J K ⋙
        RightDerived.Cochain.functor
          (Sheaf.Γ (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) :=
  whiskerRight (derivedUnit J K)
      (RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v})) ≫
    (associator (inverseImageDerived J K) (directImageDerived J K)
        (RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v}))).hom ≫
    whiskerLeft (inverseImageDerived J K) (rGammaDirectImageIso J K).hom

/-- `rGammaInverseImageComparison` is the derived unit of `a⁻¹ ⊣ Ra_*`, reassociated and
postcomposed with the Leray identification `rGammaDirectImageIso`. -/
theorem rGammaInverseImageComparison_eq :
    rGammaInverseImageComparison J K =
      whiskerRight (derivedUnit J K)
          (RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v})) ≫
        (associator (inverseImageDerived J K) (directImageDerived J K)
            (RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v}))).hom ≫
        whiskerLeft (inverseImageDerived J K) (rGammaDirectImageIso J K).hom :=
  sorry

/-- The component of `rGammaInverseImageComparison` at `E` is `RΓ(C, E) ⟶ RΓ((C / K)_total, a⁻¹ E)`. -/
theorem rGammaInverseImageComparison_app
    (E : DerivedCategory (Sheaf J AddCommGrpCat.{max w u v})) :
    (rGammaInverseImageComparison J K).app E =
      (RightDerived.Cochain.functor (Sheaf.Γ J AddCommGrpCat.{max w u v})).map
          ((derivedUnit J K).app E) ≫
        (rGammaDirectImageIso J K).hom.app ((inverseImageDerived J K).obj E) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
