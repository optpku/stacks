/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.DerivedSystem.Cocycle
public import ReasLib.CategoryTheory.Sites.Simplicial.DerivedSystem.Restriction

/-!
# Cartesian derived systems from coface cocycles on component sites
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram.{u, v, w} C J]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

namespace AbelianDerived

/-- The canonical derived inverse-image composition comparisons are associative. -/
theorem inverseImageCompIso_isAssociative :
    CategoryTheory.SimplicialSites.DerivedSystem.IsAssociative (fun n ↦ (J n).toGrothendieck)
      (fun φ ↦ (abelianInverseImageExact C J φ).obj) (inverseImageCompIso C J) := sorry

end AbelianDerived

/-- A coface cocycle on the degree-zero derived abelian sheaf determines a system
on component sites, with last-vertex inverse images and canonical edge-pullback transitions. -/
def ofCocycleOnComponents
    (K0 : DerivedCategory (Sheaf (J ⦋0⦌).toGrothendieck AddCommGrpCat.{w}))
    (α : ((abelianInverseImageExact C J (SimplexCategory.δ (1 : Fin 2))).obj).mapDerivedCategory.obj K0 ≅
      ((abelianInverseImageExact C J (SimplexCategory.δ (0 : Fin 2))).obj).mapDerivedCategory.obj K0)
    (h : CategoryTheory.SimplicialSites.DerivedSystem.cocycleLeft (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ (abelianInverseImageExact C J φ).obj) (AbelianDerived.inverseImageCompIso C J) α =
      CategoryTheory.SimplicialSites.DerivedSystem.cocycleRight (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ (abelianInverseImageExact C J φ).obj) (AbelianDerived.inverseImageCompIso C J) α) :
    CategoryTheory.SimplicialSites.DerivedSystem (fun n ↦ (J n).toGrothendieck)
      (fun φ ↦ (abelianInverseImageExact C J φ).obj) (AbelianDerived.inverseImageCompIso C J) :=
  CategoryTheory.SimplicialSites.DerivedSystem.ofCocycle (fun n ↦ (J n).toGrothendieck)
    (fun φ ↦ (abelianInverseImageExact C J φ).obj) (AbelianDerived.inverseImageCompIso C J)
    (AbelianDerived.inverseImageCompIso_isAssociative C J) K0 α h

/-- The system constructed from a coface cocycle on component sites is cartesian. -/
theorem ofCocycleOnComponents_isCartesian
    (K0 : DerivedCategory (Sheaf (J ⦋0⦌).toGrothendieck AddCommGrpCat.{w}))
    (α : ((abelianInverseImageExact C J (SimplexCategory.δ (1 : Fin 2))).obj).mapDerivedCategory.obj K0 ≅
      ((abelianInverseImageExact C J (SimplexCategory.δ (0 : Fin 2))).obj).mapDerivedCategory.obj K0)
    (h : CategoryTheory.SimplicialSites.DerivedSystem.cocycleLeft (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ (abelianInverseImageExact C J φ).obj) (AbelianDerived.inverseImageCompIso C J) α =
      CategoryTheory.SimplicialSites.DerivedSystem.cocycleRight (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ (abelianInverseImageExact C J φ).obj) (AbelianDerived.inverseImageCompIso C J) α) :
    CategoryTheory.SimplicialSites.DerivedSystem.IsCartesian (ofCocycleOnComponents C J K0 α h) :=
  CategoryTheory.SimplicialSites.DerivedSystem.ofCocycle_isCartesian (fun n ↦ (J n).toGrothendieck)
    (fun φ ↦ (abelianInverseImageExact C J φ).obj) (AbelianDerived.inverseImageCompIso C J)
    (AbelianDerived.inverseImageCompIso_isAssociative C J) K0 α h

end CategoryTheory.SimplicialSites
