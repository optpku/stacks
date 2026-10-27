/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DerivedBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Presentation

/-!
# Represented-site derived étale base change
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
variable [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y']

variable {F' G' : AlgebraicSpace S}
variable (eX' : F'.toGroupoids ≌ fibreProductApex f g)
variable (eY' : G'.toGroupoids ≌ Y')
variable [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (fibreProductApex f g).etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F') AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G') AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.spacesEtaleTopology F') AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F') (Type u)]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G') (Type u)]
variable [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (fibreProductApex f g).totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor (fibreProductFst f g)).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F')ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F' (fibreProductApex f g) eX').op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G')ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G' Y' eY').op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F')ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor F' (fibreProductApex f g) eX').op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G')ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor G' Y' eY').op.HasPointwiseRightKanExtension P]
variable [(forget RingCat.{u}).PreservesRightKanExtensions
    (smallEtaleFunctor F' (fibreProductApex f g) eX').op]
variable [(forget RingCat.{u}).PreservesRightKanExtensions
    (smallEtaleFunctor G' Y' eY').op]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F')ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F' (fibreProductApex f g) eX').op.HasLeftKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G')ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G' Y' eY').op.HasLeftKanExtension P]
variable [∀ P : X.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : Y'.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor g).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (fibreProductApex f g).totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor (fibreProductFst f g)).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (fibreProductApex f g).totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor (fibreProductSnd f g)).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (fibreProductApex f g).totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor (fibreProductFst f g ≫ g)).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (fibreProductApex f g).totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor (fibreProductSnd f g ≫ f)).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : F'.toGroupoids.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map
          (moduleComparisonSpaceMorphism (fibreProductFst f g) eX' eY'))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : F'.toGroupoids.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map
          (moduleComparisonSpaceMorphism (fibreProductFst f g) eX' eY'))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor f).toFunctor.op]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor (fibreProductFst f g)).toFunctor.op]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map
          (moduleComparisonSpaceMorphism (fibreProductFst f g) eX' eY'))).toFunctor.op]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf Y.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf Y'.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (fibreProductApex f g).etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (AlgebraicSpace.smallEtaleTopology F') AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (AlgebraicSpace.smallEtaleTopology G') AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf Y.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf Y'.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory
    (Sheaf (fibreProductApex f g).etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory
    (Sheaf (AlgebraicSpace.smallEtaleTopology F') AddCommGrpCat.{u})]
variable [HasDerivedCategory
    (Sheaf (AlgebraicSpace.smallEtaleTopology G') AddCommGrpCat.{u})]
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
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism (fibreProductFst f g) eX' eY')))
    (HomologicalComplex.quasiIso
      (Sheaf (AlgebraicSpace.smallEtaleTopology F') AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleAbelianPushforward (fibreProductFst f g) ⋙ restrictAbelian eY'))
    (HomologicalComplex.quasiIso
      (Sheaf (fibreProductApex f g).etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (restrictAbelian eX' ⋙
        AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism (fibreProductFst f g) eX' eY')))
    (HomologicalComplex.quasiIso
      (Sheaf (fibreProductApex f g).etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [X.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Y.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Y'.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [(fibreProductApex f g).etaleTopology.WEqualsLocallyBijective
    AddCommGrpCat.{u}]
variable [(AlgebraicSpace.smallEtaleTopology F').WEqualsLocallyBijective
    AddCommGrpCat.{u}]
variable [(AlgebraicSpace.smallEtaleTopology G').WEqualsLocallyBijective
    AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite (fibreProductApex f g)).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (AlgebraicSpace.ringedSite F').structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (AlgebraicSpace.ringedSite G').structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (etaleRingedSite Y').structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (etaleRingedSite (fibreProductApex f g)).structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (AlgebraicSpace.ringedSite F').structureSheaf)]
variable [HasDerivedCategory
    (SheafOfModules.{u} (AlgebraicSpace.ringedSite G').structureSheaf)]
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
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (AlgebraicSpace.ringedToposHom
        (moduleComparisonSpaceMorphism (fibreProductFst f g) eX' eY')).modulePushforward)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (AlgebraicSpace.ringedSite F').structureSheaf) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModuleDirectImage (fibreProductFst f g) ⋙
        (piToposHom G' Y' eY').modulePushforward))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite (fibreProductApex f g)).structureSheaf)
      (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((piToposHom F' (fibreProductApex f g) eX').modulePushforward ⋙
        (AlgebraicSpace.ringedToposHom
          (moduleComparisonSpaceMorphism (fibreProductFst f g) eX' eY')).modulePushforward))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite (fibreProductApex f g)).structureSheaf)
      (up ℤ))]

/-- The functorial derived identification
`g⁻¹ (Rf_* -)|_{G'_étale} ≅ Rf'_small,* (((g')⁻¹ -)|_{F'_étale})` on abelian
étale sheaves. -/
def compareRepresentableMorphismCohomologyIso :
    DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0 ⋙
      (RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
        (etaleAbelianInverseImage g).mapDerivedCategory ⋙
          (restrictAbelian eY').mapDerivedCategory) ≅
    DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0 ⋙
      ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
        (restrictAbelian eX').mapDerivedCategory ⋙
          RightDerived.Cochain.functor
            (AlgebraicSpace.EtaleAdditive.directImage
              (moduleComparisonSpaceMorphism (fibreProductFst f g) eX' eY'))) :=
  (Functor.associator (DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0) (RightDerived.Cochain.functor (etaleAbelianPushforward f))
    ((etaleAbelianInverseImage g).mapDerivedCategory ⋙ (restrictAbelian eY').mapDerivedCategory)).symm ≪≫
  isoWhiskerLeft (DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0)
    (Functor.associator (RightDerived.Cochain.functor (etaleAbelianPushforward f)) (etaleAbelianInverseImage g).mapDerivedCategory (restrictAbelian eY').mapDerivedCategory).symm ≪≫
  isoWhiskerRight (etaleAbelianDerivedBaseChangeIso f g) (restrictAbelian eY').mapDerivedCategory ≪≫
  Functor.associator (DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0) ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙ RightDerived.Cochain.functor (etaleAbelianPushforward (fibreProductFst f g))) (restrictAbelian eY').mapDerivedCategory ≪≫
  isoWhiskerLeft (DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0)
    (Functor.associator ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory) (RightDerived.Cochain.functor (etaleAbelianPushforward (fibreProductFst f g))) (restrictAbelian eY').mapDerivedCategory) ≪≫
  isoWhiskerLeft (DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0)
    (isoWhiskerLeft ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory)
      (compareMorphismCohomologyIso eX' eY' (fibreProductFst f g)
        (AlgebraicSpace.toGroupoids.presentationIso eX'.symm eY'.symm
          (fibreProductFst f g))))

/-- The functorial derived identification
`g⁻¹ (Rf_* -)|_{G'_étale} ≅ Rf'_small,* (((g')⁻¹ -)|_{F'_étale})` on étale
modules. -/
def compareRepresentableMorphismCohomology_modulesIso :
    DerivedCategory.singleFunctor (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0 ⋙
      (RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
        (etaleModuleInverseImage g).mapDerivedCategory ⋙
          ((piToposHom G' Y' eY').modulePushforward).mapDerivedCategory) ≅
    DerivedCategory.singleFunctor (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0 ⋙
      ((etaleModuleInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙
        ((piToposHom F' (fibreProductApex f g) eX').modulePushforward).mapDerivedCategory ⋙
          RightDerived.Cochain.functor
            (AlgebraicSpace.ringedToposHom
              (moduleComparisonSpaceMorphism (fibreProductFst f g) eX' eY')).modulePushforward) :=
  (Functor.associator (DerivedCategory.singleFunctor (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0) (RightDerived.Cochain.functor (etaleModuleDirectImage f))
    ((etaleModuleInverseImage g).mapDerivedCategory ⋙ ((piToposHom G' Y' eY').modulePushforward).mapDerivedCategory)).symm ≪≫
  isoWhiskerLeft (DerivedCategory.singleFunctor (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0)
    (Functor.associator (RightDerived.Cochain.functor (etaleModuleDirectImage f)) (etaleModuleInverseImage g).mapDerivedCategory ((piToposHom G' Y' eY').modulePushforward).mapDerivedCategory).symm ≪≫
  isoWhiskerRight (etaleModuleDerivedBaseChangeIso f g) ((piToposHom G' Y' eY').modulePushforward).mapDerivedCategory ≪≫
  Functor.associator (DerivedCategory.singleFunctor (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0) ((etaleModuleInverseImage (fibreProductSnd f g)).mapDerivedCategory ⋙ RightDerived.Cochain.functor (etaleModuleDirectImage (fibreProductFst f g))) ((piToposHom G' Y' eY').modulePushforward).mapDerivedCategory ≪≫
  isoWhiskerLeft (DerivedCategory.singleFunctor (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0)
    (Functor.associator ((etaleModuleInverseImage (fibreProductSnd f g)).mapDerivedCategory) (RightDerived.Cochain.functor (etaleModuleDirectImage (fibreProductFst f g))) ((piToposHom G' Y' eY').modulePushforward).mapDerivedCategory) ≪≫
  isoWhiskerLeft (DerivedCategory.singleFunctor (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0)
    (isoWhiskerLeft ((etaleModuleInverseImage (fibreProductSnd f g)).mapDerivedCategory)
      (compareMorphismCohomology_modulesIso eX' eY' (fibreProductFst f g)
        (AlgebraicSpace.toGroupoids.presentationIso eX'.symm eY'.symm
          (fibreProductFst f g))))

/-- for an abelian étale sheaf ℱ on X,
g⁻¹ (Rf_* ℱ)|_{G'_étale} ≅ Rf'_small,* (((g')⁻¹ ℱ)|_{F'_étale}) in D(G'_étale). -/
def compareRepresentableMorphismCohomology
    (ℱ : Sheaf X.etaleTopology AddCommGrpCat.{u}) :
    ((restrictAbelian eY').mapDerivedCategory).obj
        ((etaleAbelianInverseImage g).mapDerivedCategory.obj
          ((RightDerived.Cochain.functor (etaleAbelianPushforward f)).obj
            ((DerivedCategory.singleFunctor
                (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj ℱ))) ≅
      (RightDerived.Cochain.functor
          (AlgebraicSpace.EtaleAdditive.directImage
            (moduleComparisonSpaceMorphism (fibreProductFst f g) eX' eY'))).obj
        ((restrictAbelian eX').mapDerivedCategory.obj
          ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor
                (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj ℱ))) :=
  (compareRepresentableMorphismCohomologyIso f g eX' eY').app ℱ

/-- Object-level form of the functorial abelian derived comparison. -/
theorem compareRepresentableMorphismCohomology_eq
    (ℱ : Sheaf X.etaleTopology AddCommGrpCat.{u}) :
    compareRepresentableMorphismCohomology f g eX' eY' ℱ =
      (compareRepresentableMorphismCohomologyIso f g eX' eY').app ℱ :=
  rfl

/-- for an étale module ℳ on X,
g⁻¹ (Rf_* ℳ)|_{G'_étale} ≅ Rf'_small,* (((g')⁻¹ ℳ)|_{F'_étale}) in D(𝒪_{G'}). -/
def compareRepresentableMorphismCohomology_modules
    (ℳ : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (((piToposHom G' Y' eY').modulePushforward).mapDerivedCategory).obj
        ((etaleModuleInverseImage g).mapDerivedCategory.obj
          ((RightDerived.Cochain.functor (etaleModuleDirectImage f)).obj
            ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0).obj
              ℳ))) ≅
      (RightDerived.Cochain.functor
          (AlgebraicSpace.ringedToposHom
            (moduleComparisonSpaceMorphism (fibreProductFst f g) eX' eY')).modulePushforward).obj
        ((((piToposHom F' (fibreProductApex f g) eX').modulePushforward).mapDerivedCategory).obj
          ((etaleModuleInverseImage (fibreProductSnd f g)).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0).obj
              ℳ))) :=
  (compareRepresentableMorphismCohomology_modulesIso f g eX' eY').app ℳ

/-- Object-level form of the functorial module derived comparison. -/
theorem compareRepresentableMorphismCohomology_modules_eq
    (ℳ : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    compareRepresentableMorphismCohomology_modules f g eX' eY' ℳ =
      (compareRepresentableMorphismCohomology_modulesIso f g eX' eY').app ℳ :=
  rfl


end AlgebraicGeometry.GroupoidsOver
