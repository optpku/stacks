module

public import stacks_project.Chap94.Lemma_94_9_8
public import stacks_project.Chap96.Lemma_96_22_3_Comparison

/-!
# Lemma 96.22.3

On a chosen 2-fibre product of algebraic stacks over `S`, if `f` is
representable by algebraic spaces and `Y'` is represented by an algebraic
space `G'`, then the apex is represented by an algebraic space `F'`, and
derived pushforward along `f` commutes with inverse image and restriction to
the small étale site of `G'`, for abelian étale sheaves and for étale modules.
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
variable {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y)
variable [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y']

/-- Lemma 96.22.3 (1): if `f` is representable by algebraic spaces and `Y'` is
represented by an algebraic space, then the chosen 2-fibre product
`fibreProductApex f g` is represented by an algebraic space. -/
@[stacks 075P]
theorem fibreProductApex_isRepresentableByAlgebraicSpace
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (hY' : IsRepresentableByAlgebraicSpace Y') :
    IsRepresentableByAlgebraicSpace (fibreProductApex f g) :=
  sorry

variable {F' G' : AlgebraicSpace S}
variable (eX' : F'.toGroupoids ≌ fibreProductApex f g)
variable (eY' : G'.toGroupoids ≌ Y')
variable (α : (fibreProductFst f g ≫ eY'.symm.hom) ≅
    (eX'.symm.hom ≫
      AlgebraicSpace.toGroupoids.map
        (inducedHom eX' eY' (fibreProductFst f g))))
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
          (inducedHom eX' eY' (fibreProductFst f g)))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F')ᵒᵖ ⥤ Type u,
    (AlgebraicSpace.smallEtaleInclusion F').op.HasPointwiseRightKanExtension P]
variable [∀ P : F'.toGroupoids.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map
          (inducedHom eX' eY' (fibreProductFst f g)))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F')ᵒᵖ ⥤ AddCommGrpCat.{u},
    (AlgebraicSpace.smallEtaleInclusion F').op.HasPointwiseRightKanExtension P]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor f).toFunctor.op]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor (fibreProductFst f g)).toFunctor.op]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map
          (inducedHom eX' eY' (fibreProductFst f g)))).toFunctor.op]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (AlgebraicSpace.smallEtaleInclusion F').op]
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
      (smallAbelianPushforward (inducedHom eX' eY' (fibreProductFst f g))))
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
        smallAbelianPushforward (inducedHom eX' eY' (fibreProductFst f g))))
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
      (etaleModuleDirectImage f ⋙ etaleModulePullback g))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModulePullback (fibreProductSnd f g) ⋙
        etaleModuleDirectImage (fibreProductFst f g)))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (AlgebraicSpace.ringedToposHom
        (inducedHom eX' eY' (fibreProductFst f g))).modulePushforward)
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
          (inducedHom eX' eY' (fibreProductFst f g))).modulePushforward))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite (fibreProductApex f g)).structureSheaf)
      (up ℤ))]

/-- Lemma 96.22.3 (2): for an abelian étale sheaf ℱ on X,
g⁻¹ (Rf_* ℱ)|_{G'_étale} ≅ Rf'_small,* (((g')⁻¹ ℱ)|_{F'_étale}) in D(G'_étale). -/
@[stacks 075P]
def compareRepresentableMorphismCohomology
    (ℱ : Sheaf X.etaleTopology AddCommGrpCat.{u}) :
    ((restrictAbelian eY').mapDerivedCategory).obj
        ((etaleAbelianInverseImage g).mapDerivedCategory.obj
          ((RightDerived.Cochain.functor (etaleAbelianPushforward f)).obj
            ((DerivedCategory.singleFunctor
                (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj ℱ))) ≅
      (RightDerived.Cochain.functor
          (smallAbelianPushforward
            (inducedHom eX' eY' (fibreProductFst f g)))).obj
        ((restrictAbelian eX').mapDerivedCategory.obj
          ((etaleAbelianInverseImage (fibreProductSnd f g)).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor
                (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj ℱ))) :=
  (compareRepresentableMorphismCohomologyIso f g eX' eY' α).app
    ((DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj
      ℱ)

/-- Object-level form of the functorial abelian derived comparison. -/
theorem compareRepresentableMorphismCohomology_eq
    (ℱ : Sheaf X.etaleTopology AddCommGrpCat.{u}) :
    compareRepresentableMorphismCohomology f g eX' eY' α ℱ =
      (compareRepresentableMorphismCohomologyIso f g eX' eY' α).app
        ((DerivedCategory.singleFunctor
            (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj ℱ) :=
  sorry

/-- Lemma 96.22.3 (3): for an étale module ℳ on X,
g⁻¹ (Rf_* ℳ)|_{G'_étale} ≅ Rf'_small,* (((g')⁻¹ ℳ)|_{F'_étale}) in D(𝒪_{G'}). -/
@[stacks 075P]
def compareRepresentableMorphismCohomology_modules
    (ℳ : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (((piToposHom G' Y' eY').modulePushforward).mapDerivedCategory).obj
        ((etaleModulePullback g).mapDerivedCategory.obj
          ((RightDerived.Cochain.functor (etaleModuleDirectImage f)).obj
            ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0).obj
              ℳ))) ≅
      (RightDerived.Cochain.functor
          (AlgebraicSpace.ringedToposHom
            (inducedHom eX' eY' (fibreProductFst f g))).modulePushforward).obj
        ((((piToposHom F' (fibreProductApex f g) eX').modulePushforward).mapDerivedCategory).obj
          ((etaleModulePullback (fibreProductSnd f g)).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0).obj
              ℳ))) :=
  (compareRepresentableMorphismCohomology_modulesIso f g eX' eY' α).app
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0).obj ℳ)

/-- Object-level form of the functorial module derived comparison. -/
theorem compareRepresentableMorphismCohomology_modules_eq
    (ℳ : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    compareRepresentableMorphismCohomology_modules f g eX' eY' α ℳ =
      (compareRepresentableMorphismCohomology_modulesIso f g eX' eY' α).app
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0).obj ℳ) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
