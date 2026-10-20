module

public import stacks_project.Chap96.Lemma_96_22_2_Comparison

/-!
# Lemma 96.22.2

If `f : X ⟶ Y` is a morphism of algebraic stacks over `S` represented by
algebraic spaces `F`, `G`, then derived pushforward along `f` commutes with
restriction to the small étale sites of `F` and `G`, for abelian étale sheaves
and for étale modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S} {F G : AlgebraicSpace S}
variable (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
variable (α : (f ≫ eY.symm.hom) ≅
    (eX.symm.hom ≫ AlgebraicSpace.toGroupoids.map (inducedHom eX eY f)))
variable [AlgebraicStack X] [AlgebraicStack Y]
variable [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.spacesEtaleTopology F) AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type u)]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G) (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor F X eX).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor F X eX).op]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor G Y eY).op]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasLeftKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasLeftKanExtension P]
variable [∀ P : X.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : F.toGroupoids.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : F.toGroupoids.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor f).toFunctor.op]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map (inducedHom eX eY f))).toFunctor.op]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf Y.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf Y.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u})]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (etaleAbelianPushforward f))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (smallAbelianPushforward (inducedHom eX eY f)))
    (HomologicalComplex.quasiIso
      (Sheaf (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleAbelianPushforward f ⋙ restrictAbelian eY))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (restrictAbelian eX ⋙ smallAbelianPushforward (inducedHom eX eY f)))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [X.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Y.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [(AlgebraicSpace.smallEtaleTopology F).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [(AlgebraicSpace.smallEtaleTopology G).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (AlgebraicSpace.ringedSite F).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (AlgebraicSpace.ringedSite G).structureSheaf)]
variable [HasDerivedCategory (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)]
variable [HasDerivedCategory (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf)]
variable [HasDerivedCategory (SheafOfModules.{u} (AlgebraicSpace.ringedSite F).structureSheaf)]
variable [HasDerivedCategory (SheafOfModules.{u} (AlgebraicSpace.ringedSite G).structureSheaf)]
variable [letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (etaleModuleDirectImage f))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (AlgebraicSpace.ringedToposHom (inducedHom eX eY f)).modulePushforward)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (AlgebraicSpace.ringedSite F).structureSheaf) (up ℤ))]
variable [letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((piToposHom F X eX).modulePushforward ⋙
        (AlgebraicSpace.ringedToposHom (inducedHom eX eY f)).modulePushforward))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]

/-- Lemma 96.22.2 (1): for an abelian étale sheaf ℱ on X,
(Rf_* ℱ)|_{G_étale} ≅ Rf_small,* (ℱ|_{F_étale}) in D(G_étale). -/
@[stacks 075N]
def compareMorphismCohomology (ℱ : Sheaf X.etaleTopology AddCommGrpCat.{u}) :
    letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    ((restrictAbelian eY).mapDerivedCategory).obj
        ((RightDerived.Cochain.functor (etaleAbelianPushforward f)).obj
          ((DerivedCategory.singleFunctor
              (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj ℱ)) ≅
      (RightDerived.Cochain.functor
          (smallAbelianPushforward (inducedHom eX eY f))).obj
        ((restrictAbelian eX).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
              (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj ℱ)) :=
  letI := hasSmallCFGTypeSections_ofRepresented f eX eY
  (compareMorphismCohomologyIso eX eY f α).app
    ((DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj ℱ)

/-- Object-level form of the functorial abelian derived comparison. -/
theorem compareMorphismCohomology_eq (ℱ : Sheaf X.etaleTopology AddCommGrpCat.{u}) :
    letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    compareMorphismCohomology eX eY f α ℱ =
      (compareMorphismCohomologyIso eX eY f α).app
        ((DerivedCategory.singleFunctor
            (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj ℱ) :=
  sorry

/-- Lemma 96.22.2 (2): for an étale module ℳ on X,
(Rf_* ℳ)|_{G_étale} ≅ Rf_small,* (ℳ|_{F_étale}) in D(𝒪_G). -/
@[stacks 075N]
def compareMorphismCohomology_modules
    (ℳ : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    (((piToposHom G Y eY).modulePushforward).mapDerivedCategory).obj
        ((RightDerived.Cochain.functor (etaleModuleDirectImage f)).obj
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0).obj ℳ)) ≅
      (RightDerived.Cochain.functor
          (AlgebraicSpace.ringedToposHom (inducedHom eX eY f)).modulePushforward).obj
        ((((piToposHom F X eX).modulePushforward).mapDerivedCategory).obj
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0).obj ℳ)) :=
  letI := hasSmallCFGTypeSections_ofRepresented f eX eY
  (compareMorphismCohomology_modulesIso eX eY f α).app
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0).obj ℳ)

/-- Object-level form of the functorial module derived comparison. -/
theorem compareMorphismCohomology_modules_eq
    (ℳ : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    compareMorphismCohomology_modules eX eY f α ℳ =
      (compareMorphismCohomology_modulesIso eX eY f α).app
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0).obj ℳ) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
