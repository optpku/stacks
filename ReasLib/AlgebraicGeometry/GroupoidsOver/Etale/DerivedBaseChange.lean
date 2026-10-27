/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.BaseChange
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right

/-!
# Derived étale base change on degree-zero sheaves
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Functor
open CategoryTheory.Sheaf.InternalModule
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

variable {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y)

variable [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (fibreProductApex f g).totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor (fibreProductFst f g)).toFunctor.op.HasPointwiseRightKanExtension P]

variable [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (fibreProductApex f g).etaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf Y.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf Y'.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (fibreProductApex f g).etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf Y.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf Y'.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory
    (Sheaf (fibreProductApex f g).etaleTopology AddCommGrpCat.{u})]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (etaleAbelianPushforward f))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleAbelianPushforward (fibreProductFst f g)))
    (HomologicalComplex.quasiIso
      (Sheaf (fibreProductApex f g).etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
        etaleAbelianPushforward (fibreProductFst f g)))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]

/-- The cochain-level unit for exact postcomposition of `Rf_*` by `g⁻¹`. -/
def etaleAbelianDerivedBaseChange_postcompUnit :
    RightDerived.Cochain.toDerived
        (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
            DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u})) ⋙
        (RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
          (etaleAbelianInverseImage g).mapDerivedCategory) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g))
        (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y'.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory (Sheaf Y'.etaleTopology AddCommGrpCat.{u}))).hom ≫
    (Functor.associator
        ((etaleAbelianPushforward f).mapHomologicalComplex (up ℤ))
        ((etaleAbelianInverseImage g).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (Sheaf Y'.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
            DerivedCategory (Sheaf Y'.etaleTopology AddCommGrpCat.{u}))).hom ≫
    (isoWhiskerLeft ((etaleAbelianPushforward f).mapHomologicalComplex (up ℤ))
      (etaleAbelianInverseImage g).mapDerivedCategoryFactors.symm).hom ≫
    (Functor.associator
        ((etaleAbelianPushforward f).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (Sheaf Y.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
            DerivedCategory (Sheaf Y.etaleTopology AddCommGrpCat.{u}))
        (etaleAbelianInverseImage g).mapDerivedCategory).inv ≫
    whiskerRight (RightDerived.Cochain.unit (etaleAbelianPushforward f))
      (etaleAbelianInverseImage g).mapDerivedCategory ≫
    (Functor.associator
        (DerivedCategory.Q :
          CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
            DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u}))
        (RightDerived.Cochain.functor (etaleAbelianPushforward f))
        (etaleAbelianInverseImage g).mapDerivedCategory).hom

/-- The comparison from `R(f_* ⋙ g⁻¹)` to `Rf_*` followed by exact inverse image. -/
def etaleAbelianDerivedBaseChange_postcomp :
    RightDerived.Cochain.functor
        (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g) ⟶
      RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
        (etaleAbelianInverseImage g).mapDerivedCategory :=
  (RightDerived.Cochain.functor
      (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))
    (RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
      (etaleAbelianInverseImage g).mapDerivedCategory)
    (etaleAbelianDerivedBaseChange_postcompUnit f g)

/-- Exact inverse image commutes with the derived postcomposition comparison. -/
instance etaleAbelianDerivedBaseChange_postcomp_isIso :
    IsIso (etaleAbelianDerivedBaseChange_postcomp f g) := sorry

/-- The cochain-level unit for exact precomposition of `Rf'_*` by `(g')⁻¹`. -/
def etaleAbelianDerivedBaseChange_precompUnit :
    RightDerived.Cochain.toDerived
        (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
          etaleAbelianPushforward (fibreProductFst f g)) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
            DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u})) ⋙
        ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
          RightDerived.Cochain.functor
            (etaleAbelianPushforward (fibreProductFst f g))) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl
          (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
            etaleAbelianPushforward (fibreProductFst f g)))
        (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y'.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory (Sheaf Y'.etaleTopology AddCommGrpCat.{u}))).hom ≫
    (Functor.associator
        ((etaleAbelianInverseImage (fibreProductSnd f g)).mapHomologicalComplex
          (up ℤ))
        ((etaleAbelianPushforward (fibreProductFst f g)).mapHomologicalComplex
          (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (Sheaf Y'.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
            DerivedCategory (Sheaf Y'.etaleTopology AddCommGrpCat.{u}))).hom ≫
    RightDerived.Composition.iteratedUnit
      (etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategoryFactors.inv
      (RightDerived.Cochain.unit (etaleAbelianPushforward (fibreProductFst f g)))

/-- The comparison from `R((g')⁻¹ ⋙ f'_*)` to `Rf'_*` after exact inverse image. -/
def etaleAbelianDerivedBaseChange_precomp :
    RightDerived.Cochain.functor
        (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
          etaleAbelianPushforward (fibreProductFst f g)) ⟶
      (etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
        RightDerived.Cochain.functor
          (etaleAbelianPushforward (fibreProductFst f g)) :=
  (RightDerived.Cochain.functor
      (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
        etaleAbelianPushforward (fibreProductFst f g))).rightDerivedDesc
    (RightDerived.Cochain.unit
      (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
        etaleAbelianPushforward (fibreProductFst f g)))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))
    ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
      RightDerived.Cochain.functor
        (etaleAbelianPushforward (fibreProductFst f g)))
    (etaleAbelianDerivedBaseChange_precompUnit f g)

/-- Derived functorial form of the underived étale abelian identification. -/
def etaleAbelianDerivedBaseChange_mapNatIso :
    RightDerived.Cochain.functor
        (etaleAbelianPushforward f ⋙ etaleAbelianInverseImage g) ≅
      RightDerived.Cochain.functor
        (etaleAbelianInverseImage (fibreProductSnd f g) ⋙
          etaleAbelianPushforward (fibreProductFst f g)) :=
  Functor.RightDerived.mapNatIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
        DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u}))
    (HomologicalComplex.quasiIso
      (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))
    (isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (etaleAbelianPushforwardBaseChangeIso f g) (up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y'.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory (Sheaf Y'.etaleTopology AddCommGrpCat.{u})))

/-- The canonical derived étale base-change transformation. -/
def etaleAbelianDerivedBaseChangeHom [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
        (etaleAbelianInverseImage g).mapDerivedCategory ⟶
      (etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
        RightDerived.Cochain.functor (etaleAbelianPushforward (fibreProductFst f g)) :=
  inv (etaleAbelianDerivedBaseChange_postcomp f g) ≫
    (etaleAbelianDerivedBaseChange_mapNatIso f g).hom ≫ etaleAbelianDerivedBaseChange_precomp f g

/-- The canonical derived base-change map on sheaves embedded in degree zero. -/
def etaleAbelianDerivedBaseChangeHomOnSheaves [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0 ⋙
        (RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
        (etaleAbelianInverseImage g).mapDerivedCategory) ⟶
      DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0 ⋙
        ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
        RightDerived.Cochain.functor (etaleAbelianPushforward (fibreProductFst f g))) :=
  whiskerLeft (DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0)
    (etaleAbelianDerivedBaseChangeHom f g)

/-- Derived étale base change is invertible on degree-zero sheaf inputs. -/
instance etaleAbelianDerivedBaseChangeHom_isIso [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    IsIso (etaleAbelianDerivedBaseChangeHomOnSheaves f g) := sorry

/-- Derived étale base change, natural in sheaves embedded in degree zero. -/
def etaleAbelianDerivedBaseChangeIso [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0 ⋙
        (RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
        (etaleAbelianInverseImage g).mapDerivedCategory) ≅
      DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0 ⋙
        ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
        RightDerived.Cochain.functor (etaleAbelianPushforward (fibreProductFst f g))) :=
  asIso (etaleAbelianDerivedBaseChangeHomOnSheaves f g)

/-- Objectwise form of `etaleAbelianDerivedBaseChangeIso`. -/
def etaleAbelianDerivedBaseChangeIso_app
 [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y']
    (ℱ : Sheaf X.etaleTopology AddCommGrpCat.{u}) :
    ((etaleAbelianInverseImage g).mapDerivedCategory).obj
        ((RightDerived.Cochain.functor (etaleAbelianPushforward f)).obj ((DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj ℱ)) ≅
      (RightDerived.Cochain.functor
          (etaleAbelianPushforward (fibreProductFst f g))).obj
        ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj ℱ)) :=
  (etaleAbelianDerivedBaseChangeIso f g).app ℱ

variable [∀ P : X.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (fibreProductApex f g).totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor (fibreProductFst f g)).toFunctor.op.HasPointwiseRightKanExtension P]

variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite (fibreProductApex f g)).structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (etaleRingedSite (fibreProductApex f g)).structureSheaf)]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (etaleModuleDirectImage f))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModuleDirectImage (fibreProductFst f g)))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite (fibreProductApex f g)).structureSheaf)
      (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModuleDirectImage f ⋙ etaleModuleInverseImage g))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModuleInverseImage (fibreProductSnd f g) ⋙
        etaleModuleDirectImage (fibreProductFst f g)))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]
/-- The cochain-level unit for exact postcomposition of module `Rf_*` by `g⁻¹`. -/
def etaleModuleDerivedBaseChange_postcompUnit :
    RightDerived.Cochain.toDerived
        (etaleModuleDirectImage f ⋙ etaleModuleInverseImage g) ⟶
      (DerivedCategory.Q :
          CochainComplex
            (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) ℤ ⥤
            DerivedCategory
              (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)) ⋙
        (RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
          (etaleModuleInverseImage g).mapDerivedCategory) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModuleDirectImage f ⋙ etaleModuleInverseImage g))
        (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex
          (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf) ℤ ⥤
          DerivedCategory
            (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf))).hom ≫
    (Functor.associator
        ((etaleModuleDirectImage f).mapHomologicalComplex (up ℤ))
        ((etaleModuleInverseImage g).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex
            (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf) ℤ ⥤
            DerivedCategory
              (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf))).hom ≫
    (isoWhiskerLeft ((etaleModuleDirectImage f).mapHomologicalComplex (up ℤ))
      (etaleModuleInverseImage g).mapDerivedCategoryFactors.symm).hom ≫
    (Functor.associator
        ((etaleModuleDirectImage f).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex
            (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf) ℤ ⥤
            DerivedCategory
              (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf))
        (etaleModuleInverseImage g).mapDerivedCategory).inv ≫
    whiskerRight (RightDerived.Cochain.unit (etaleModuleDirectImage f))
      (etaleModuleInverseImage g).mapDerivedCategory ≫
    (Functor.associator
        (DerivedCategory.Q :
          CochainComplex
            (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) ℤ ⥤
            DerivedCategory
              (SheafOfModules.{u} (etaleRingedSite X).structureSheaf))
        (RightDerived.Cochain.functor (etaleModuleDirectImage f))
        (etaleModuleInverseImage g).mapDerivedCategory).hom

/-- The comparison from `R(f_* ⋙ g⁻¹)` to module `Rf_*` followed by exact inverse
image. -/
def etaleModuleDerivedBaseChange_postcomp :
    RightDerived.Cochain.functor
        (etaleModuleDirectImage f ⋙ etaleModuleInverseImage g) ⟶
      RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
        (etaleModuleInverseImage g).mapDerivedCategory :=
  (RightDerived.Cochain.functor
      (etaleModuleDirectImage f ⋙ etaleModuleInverseImage g)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (etaleModuleDirectImage f ⋙ etaleModuleInverseImage g))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))
    (RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
      (etaleModuleInverseImage g).mapDerivedCategory)
    (etaleModuleDerivedBaseChange_postcompUnit f g)

/-- Exact inverse image commutes with the derived postcomposition comparison. -/
instance etaleModuleDerivedBaseChange_postcomp_isIso :
    IsIso (etaleModuleDerivedBaseChange_postcomp f g) := sorry

/-- The cochain-level unit for exact precomposition of module `Rf'_*` by
`(g')⁻¹`. -/
def etaleModuleDerivedBaseChange_precompUnit :
    RightDerived.Cochain.toDerived
        (etaleModuleInverseImage (fibreProductSnd f g) ⋙
          etaleModuleDirectImage (fibreProductFst f g)) ⟶
      (DerivedCategory.Q :
          CochainComplex
            (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) ℤ ⥤
            DerivedCategory
              (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)) ⋙
        ((etaleModuleInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
          RightDerived.Cochain.functor
            (etaleModuleDirectImage (fibreProductFst f g))) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl
          (etaleModuleInverseImage (fibreProductSnd f g) ⋙
            etaleModuleDirectImage (fibreProductFst f g)))
        (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex
          (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf) ℤ ⥤
          DerivedCategory
            (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf))).hom ≫
    (Functor.associator
        ((etaleModuleInverseImage (fibreProductSnd f g)).mapHomologicalComplex
          (up ℤ))
        ((etaleModuleDirectImage (fibreProductFst f g)).mapHomologicalComplex
          (up ℤ))
        (DerivedCategory.Q :
          CochainComplex
            (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf) ℤ ⥤
            DerivedCategory
              (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf))).hom ≫
    RightDerived.Composition.iteratedUnit
      (etaleModuleInverseImage (fibreProductSnd f g)).mapDerivedCategoryFactors.inv
      (RightDerived.Cochain.unit
        (etaleModuleDirectImage (fibreProductFst f g)))

/-- The comparison from `R((g')⁻¹ ⋙ f'_*)` to module `Rf'_*` after exact inverse
image. -/
def etaleModuleDerivedBaseChange_precomp :
    RightDerived.Cochain.functor
        (etaleModuleInverseImage (fibreProductSnd f g) ⋙
          etaleModuleDirectImage (fibreProductFst f g)) ⟶
      (etaleModuleInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
        RightDerived.Cochain.functor
          (etaleModuleDirectImage (fibreProductFst f g)) :=
  (RightDerived.Cochain.functor
      (etaleModuleInverseImage (fibreProductSnd f g) ⋙
        etaleModuleDirectImage (fibreProductFst f g))).rightDerivedDesc
    (RightDerived.Cochain.unit
      (etaleModuleInverseImage (fibreProductSnd f g) ⋙
        etaleModuleDirectImage (fibreProductFst f g)))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))
    ((etaleModuleInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
      RightDerived.Cochain.functor
        (etaleModuleDirectImage (fibreProductFst f g)))
    (etaleModuleDerivedBaseChange_precompUnit f g)

/-- Derived functorial form of the underived étale module identification. -/
def etaleModuleDerivedBaseChange_mapNatIso :
    RightDerived.Cochain.functor
        (etaleModuleDirectImage f ⋙ etaleModuleInverseImage g) ≅
      RightDerived.Cochain.functor
        (etaleModuleInverseImage (fibreProductSnd f g) ⋙
          etaleModuleDirectImage (fibreProductFst f g)) :=
  Functor.RightDerived.mapNatIso
    (DerivedCategory.Q :
      CochainComplex (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) ℤ ⥤
        DerivedCategory
          (SheafOfModules.{u} (etaleRingedSite X).structureSheaf))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))
    (isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (etaleModulePushforwardBaseChangeIso f g) (up ℤ))
      (DerivedCategory.Q :
        CochainComplex
          (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf) ℤ ⥤
          DerivedCategory
            (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf)))

/-- The canonical derived étale base-change transformation. -/
def etaleModuleDerivedBaseChangeHom [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
        (etaleModuleInverseImage g).mapDerivedCategory ⟶
      (etaleModuleInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
        RightDerived.Cochain.functor (etaleModuleDirectImage (fibreProductFst f g)) :=
  inv (etaleModuleDerivedBaseChange_postcomp f g) ≫
    (etaleModuleDerivedBaseChange_mapNatIso f g).hom ≫ etaleModuleDerivedBaseChange_precomp f g

/-- The canonical derived base-change map on sheaves embedded in degree zero. -/
def etaleModuleDerivedBaseChangeHomOnSheaves [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    DerivedCategory.singleFunctor (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0 ⋙
        (RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
        (etaleModuleInverseImage g).mapDerivedCategory) ⟶
      DerivedCategory.singleFunctor (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0 ⋙
        ((etaleModuleInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
        RightDerived.Cochain.functor (etaleModuleDirectImage (fibreProductFst f g))) :=
  whiskerLeft (DerivedCategory.singleFunctor (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0)
    (etaleModuleDerivedBaseChangeHom f g)

/-- Derived étale base change is invertible on degree-zero sheaf inputs. -/
instance etaleModuleDerivedBaseChangeHom_isIso [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    IsIso (etaleModuleDerivedBaseChangeHomOnSheaves f g) := sorry

/-- Derived étale base change, natural in sheaves embedded in degree zero. -/
def etaleModuleDerivedBaseChangeIso [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] :
    DerivedCategory.singleFunctor (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0 ⋙
        (RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
        (etaleModuleInverseImage g).mapDerivedCategory) ≅
      DerivedCategory.singleFunctor (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0 ⋙
        ((etaleModuleInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
        RightDerived.Cochain.functor (etaleModuleDirectImage (fibreProductFst f g))) :=
  asIso (etaleModuleDerivedBaseChangeHomOnSheaves f g)


end AlgebraicGeometry.GroupoidsOver
