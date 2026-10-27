/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DerivedComparison
public import stacks_project.Chap96.Lemma_96_10_3_Comparison
public import stacks_project.Chap96.Lemma_96_22_1_Restriction

/-!
# Comparison of derived étale pushforwards

Compatibility notation and the functorial comparison for representing algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open CategoryTheory.Functor FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Direct image of abelian sheaves along a morphism of algebraic spaces. -/
abbrev smallAbelianPushforward {A B : AlgebraicSpace S} (h : A ⟶ B) :
    Sheaf (AlgebraicSpace.smallEtaleTopology A) AddCommGrpCat.{u} ⥤
      Sheaf (AlgebraicSpace.smallEtaleTopology B) AddCommGrpCat.{u} :=
  AlgebraicSpace.EtaleAdditive.directImage h

variable {X Y : GroupoidsOver S} {F G : AlgebraicSpace S}
variable (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
variable [HasSmallCFGTypeSections (S := S) f]
variable (α : (f ≫ eY.symm.hom) ≅
    (eX.symm.hom ≫ AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY)))
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
        (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : F.toGroupoids.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor f).toFunctor.op]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY))).toFunctor.op]
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
    (RightDerived.Cochain.toDerived (AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY)))
    (HomologicalComplex.quasiIso
      (Sheaf (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleAbelianPushforward f ⋙ restrictAbelian eY))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (restrictAbelian eX ⋙ AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY)))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]
#check (AlgebraicGeometry.GroupoidsOver.compareMorphismCohomologyIso eX eY f α :
    RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
        (restrictAbelian eY).mapDerivedCategory ≅
      (restrictAbelian eX).mapDerivedCategory ⋙
        RightDerived.Cochain.functor
          (AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY)))

end AlgebraicGeometry.GroupoidsOver
