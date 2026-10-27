/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.DerivedPushforward.BaseChange
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor ComplexShape
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}
variable {X Y Y' : GroupoidsOver S} (f : X ⟶ Y) (g : Y' ⟶ Y) (τ : StandardTopology)
variable [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y']

section Abelian

variable [HasDerivedCategory (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (Y'.associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory
    (Sheaf ((fibreProductApex f g).associatedTopology τ) AddCommGrpCat.{u + 1})]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (abelianPushforward f τ))
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (abelianPushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (Sheaf ((fibreProductApex f g).associatedTopology τ) AddCommGrpCat.{u + 1})
      (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (abelianPushforward f τ ⋙ associatedAbelianInverseImage g τ))
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (associatedAbelianInverseImage (fibreProductSnd f g) τ ⋙
        abelianPushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) (up ℤ))]

/- Lemma 96.21.3 (1): Canonical derived base change for abelian sheaves,
natural in sheaves embedded in degree zero. -/
@[stacks 075H] #check
  (AlgebraicGeometry.GroupoidsOver.DerivedPushforward.abelianBaseChangeIso f g τ :
    DerivedCategory.singleFunctor (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) 0 ⋙
        (DerivedPushforward.abelian f τ ⋙ (associatedAbelianInverseImage g τ).mapDerivedCategory) ≅
      DerivedCategory.singleFunctor (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) 0 ⋙
        ((associatedAbelianInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
          DerivedPushforward.abelian (fibreProductFst f g) τ))

end Abelian

section Modules

variable [HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Y'.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable [HasSheafify ((fibreProductApex f g).associatedTopology τ) AddCommGrpCat.{u + 1}]

variable [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))]
variable [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y τ))]
variable [HasDerivedCategory (SheafOfModules.{u + 1} (associatedStructureSheaf Y' τ))]
variable [HasDerivedCategory
    (SheafOfModules.{u + 1} (associatedStructureSheaf (fibreProductApex f g) τ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (modulePushforward f τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (modulePushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf (fibreProductApex f g) τ))
      (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (modulePushforward f τ ⋙ associatedModuleInverseImage g τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (associatedModuleInverseImage (fibreProductSnd f g) τ ⋙
        modulePushforward (fibreProductFst f g) τ))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (up ℤ))]

/- Lemma 96.21.3 (2): Canonical derived base change for module sheaves,
natural in sheaves embedded in degree zero. -/
@[stacks 075H] #check
  (AlgebraicGeometry.GroupoidsOver.DerivedPushforward.moduleBaseChangeIso f g τ :
    DerivedCategory.singleFunctor (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) 0 ⋙
        (DerivedPushforward.modules f τ ⋙ (associatedModuleInverseImage g τ).mapDerivedCategory) ≅
      DerivedCategory.singleFunctor (SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) 0 ⋙
        ((associatedModuleInverseImage (fibreProductSnd f g) τ).mapDerivedCategory ⋙
          DerivedPushforward.modules (fibreProductFst f g) τ))

end Modules

end AlgebraicGeometry.GroupoidsOver
