/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.DerivedSystem.Cocycle
public import ReasLib.CategoryTheory.Sites.Grothendieck.DerivedSystem

/-!
# Cartesian derived systems from coface cocycles on fiber sites
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

namespace AbelianDerived

/-- The canonical derived inverse-image composition comparisons are associative. -/
theorem inverseImageCompIso_isAssociative :
    CategoryTheory.SimplicialSites.DerivedSystem.IsAssociative (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ (abelianInverseImageExact F J φ).obj) (inverseImageCompIso F J) := sorry

end AbelianDerived

/-- A coface cocycle on the degree-zero derived abelian sheaf determines a system
on fiber sites, with last-vertex inverse images and canonical edge-pullback transitions. -/
def ofCocycle
    (K0 : DerivedCategory (Sheaf (J (op ⦋0⦌)).toGrothendieck AddCommGrpCat.{w}))
    (α : ((abelianInverseImageExact F J (SimplexCategory.δ (1 : Fin 2))).obj).mapDerivedCategory.obj K0 ≅
      ((abelianInverseImageExact F J (SimplexCategory.δ (0 : Fin 2))).obj).mapDerivedCategory.obj K0)
    (h : CategoryTheory.SimplicialSites.DerivedSystem.cocycleLeft (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ (abelianInverseImageExact F J φ).obj) (AbelianDerived.inverseImageCompIso F J) α =
      CategoryTheory.SimplicialSites.DerivedSystem.cocycleRight (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ (abelianInverseImageExact F J φ).obj) (AbelianDerived.inverseImageCompIso F J) α) :
    CategoryTheory.SimplicialSites.DerivedSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ (abelianInverseImageExact F J φ).obj) (AbelianDerived.inverseImageCompIso F J) :=
  CategoryTheory.SimplicialSites.DerivedSystem.ofCocycle (fun n ↦ (J (op n)).toGrothendieck)
    (fun φ ↦ (abelianInverseImageExact F J φ).obj) (AbelianDerived.inverseImageCompIso F J)
    (AbelianDerived.inverseImageCompIso_isAssociative F J) K0 α h

/-- The system constructed from a coface cocycle on fiber sites is cartesian. -/
theorem ofCocycle_isCartesian
    (K0 : DerivedCategory (Sheaf (J (op ⦋0⦌)).toGrothendieck AddCommGrpCat.{w}))
    (α : ((abelianInverseImageExact F J (SimplexCategory.δ (1 : Fin 2))).obj).mapDerivedCategory.obj K0 ≅
      ((abelianInverseImageExact F J (SimplexCategory.δ (0 : Fin 2))).obj).mapDerivedCategory.obj K0)
    (h : CategoryTheory.SimplicialSites.DerivedSystem.cocycleLeft (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ (abelianInverseImageExact F J φ).obj) (AbelianDerived.inverseImageCompIso F J) α =
      CategoryTheory.SimplicialSites.DerivedSystem.cocycleRight (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ (abelianInverseImageExact F J φ).obj) (AbelianDerived.inverseImageCompIso F J) α) :
    CategoryTheory.SimplicialSites.DerivedSystem.IsCartesian (ofCocycle F J K0 α h) :=
  CategoryTheory.SimplicialSites.DerivedSystem.ofCocycle_isCartesian (fun n ↦ (J (op n)).toGrothendieck)
    (fun φ ↦ (abelianInverseImageExact F J φ).obj) (AbelianDerived.inverseImageCompIso F J)
    (AbelianDerived.inverseImageCompIso_isAssociative F J) K0 α h

end CategoryTheory.Grothendieck
