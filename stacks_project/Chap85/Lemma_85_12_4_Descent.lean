/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Definition_85_12_1_Cartesian
public import ReasLib.CategoryTheory.Sites.Simplicial.FaceDescent

/-! Compatibility checks for coface descent on a simplicial site. -/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u v w

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : CategoryTheory.SimplicialSites.IsMorphismDiagram.{u, v, w} C J]
variable (A : Type (w + 1)) [Category.{w} A]
variable [instWeakSheafifyA : ∀ n, HasWeakSheafify (J n).toGrothendieck A]
variable [instLeftKanA : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ A),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include instMorphismDiagram instWeakSheafify instLeftKan instWeakSheafifyA instLeftKanA

#check (CategoryTheory.SimplicialSites.Sheaf.FaceDescent C J A : Cat)

#check (CategoryTheory.SimplicialSites.Sheaf.facePullback C J A :
  ∀ (i : Fin 3) {F : Sheaf ((J ⦋0⦌).toGrothendieck) A}
    (α : ((C.map (SimplexCategory.δ (1 : Fin 2))).toFunctor.sheafPullback A
      (J ⦋0⦌).toGrothendieck (J ⦋1⦌).toGrothendieck).obj F ≅
      ((C.map (SimplexCategory.δ (0 : Fin 2))).toFunctor.sheafPullback A
        (J ⦋0⦌).toGrothendieck (J ⦋1⦌).toGrothendieck).obj F),
    ((C.map (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ i)).toFunctor.sheafPullback A
      (J ⦋0⦌).toGrothendieck (J ⦋2⦌).toGrothendieck).obj F ⟶
      ((C.map (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ i)).toFunctor.sheafPullback A
        (J ⦋0⦌).toGrothendieck (J ⦋2⦌).toGrothendieck).obj F)

#check (CategoryTheory.SimplicialSites.Sheaf.facePullback_eq C J A :
  ∀ (i : Fin 3) {F : Sheaf ((J ⦋0⦌).toGrothendieck) A}
    (α : ((C.map (SimplexCategory.δ (1 : Fin 2))).toFunctor.sheafPullback A
      (J ⦋0⦌).toGrothendieck (J ⦋1⦌).toGrothendieck).obj F ≅
      ((C.map (SimplexCategory.δ (0 : Fin 2))).toFunctor.sheafPullback A
        (J ⦋0⦌).toGrothendieck (J ⦋1⦌).toGrothendieck).obj F),
    CategoryTheory.SimplicialSites.Sheaf.facePullback C J A i α =
      (CategoryTheory.SimplicialSites.Sheaf.inverseImageCompIso C J A (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.δ i)).hom.app F ≫
        ((C.map (SimplexCategory.δ i)).toFunctor.sheafPullback A
          (J ⦋1⦌).toGrothendieck (J ⦋2⦌).toGrothendieck).map α.hom ≫
        (CategoryTheory.SimplicialSites.Sheaf.inverseImageCompIso C J A (SimplexCategory.δ (0 : Fin 2))
            (SimplexCategory.δ i)).inv.app F)

#check (CategoryTheory.SimplicialSites.Sheaf.cocycleLeft C J A :
  ∀ {F : Sheaf ((J ⦋0⦌).toGrothendieck) A}
    (α : ((C.map (SimplexCategory.δ (1 : Fin 2))).toFunctor.sheafPullback A
      (J ⦋0⦌).toGrothendieck (J ⦋1⦌).toGrothendieck).obj F ≅
      ((C.map (SimplexCategory.δ (0 : Fin 2))).toFunctor.sheafPullback A
        (J ⦋0⦌).toGrothendieck (J ⦋1⦌).toGrothendieck).obj F),
    ((C.map (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).toFunctor.sheafPullback A
      (J ⦋0⦌).toGrothendieck (J ⦋2⦌).toGrothendieck).obj F ⟶
      ((C.map (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).toFunctor.sheafPullback A
        (J ⦋0⦌).toGrothendieck (J ⦋2⦌).toGrothendieck).obj F)

#check (CategoryTheory.SimplicialSites.Sheaf.cocycleLeft_eq C J A :
  ∀ {F : Sheaf ((J ⦋0⦌).toGrothendieck) A}
    (α : ((C.map (SimplexCategory.δ (1 : Fin 2))).toFunctor.sheafPullback A
      (J ⦋0⦌).toGrothendieck (J ⦋1⦌).toGrothendieck).obj F ≅
      ((C.map (SimplexCategory.δ (0 : Fin 2))).toFunctor.sheafPullback A
        (J ⦋0⦌).toGrothendieck (J ⦋1⦌).toGrothendieck).obj F),
    CategoryTheory.SimplicialSites.Sheaf.cocycleLeft C J A α =
      (CategoryTheory.SimplicialSites.Sheaf.recodeInverseImage C J A
          (SimplexCategory.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app F ≫
        CategoryTheory.SimplicialSites.Sheaf.facePullback C J A 1 α)

#check (CategoryTheory.SimplicialSites.Sheaf.cocycleRight C J A :
  ∀ {F : Sheaf ((J ⦋0⦌).toGrothendieck) A}
    (α : ((C.map (SimplexCategory.δ (1 : Fin 2))).toFunctor.sheafPullback A
      (J ⦋0⦌).toGrothendieck (J ⦋1⦌).toGrothendieck).obj F ≅
      ((C.map (SimplexCategory.δ (0 : Fin 2))).toFunctor.sheafPullback A
        (J ⦋0⦌).toGrothendieck (J ⦋1⦌).toGrothendieck).obj F),
    ((C.map (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).toFunctor.sheafPullback A
      (J ⦋0⦌).toGrothendieck (J ⦋2⦌).toGrothendieck).obj F ⟶
      ((C.map (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).toFunctor.sheafPullback A
        (J ⦋0⦌).toGrothendieck (J ⦋2⦌).toGrothendieck).obj F)

#check (CategoryTheory.SimplicialSites.Sheaf.cocycleRight_eq C J A :
  ∀ {F : Sheaf ((J ⦋0⦌).toGrothendieck) A}
    (α : ((C.map (SimplexCategory.δ (1 : Fin 2))).toFunctor.sheafPullback A
      (J ⦋0⦌).toGrothendieck (J ⦋1⦌).toGrothendieck).obj F ≅
      ((C.map (SimplexCategory.δ (0 : Fin 2))).toFunctor.sheafPullback A
        (J ⦋0⦌).toGrothendieck (J ⦋1⦌).toGrothendieck).obj F),
    CategoryTheory.SimplicialSites.Sheaf.cocycleRight C J A α =
      CategoryTheory.SimplicialSites.Sheaf.facePullback C J A 2 α ≫
        (CategoryTheory.SimplicialSites.Sheaf.recodeInverseImage C J A
            (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
              (Fin.zero_le _))).hom.app F ≫
        CategoryTheory.SimplicialSites.Sheaf.facePullback C J A 0 α ≫
        (CategoryTheory.SimplicialSites.Sheaf.recodeInverseImage C J A
            (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
              le_rfl).symm).hom.app F)
