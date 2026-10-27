/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.DerivedSystem.Cocycle.Components
public import ReasLib.CategoryTheory.Sites.Grothendieck.DerivedSystem.Cocycle
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open scoped Simplicial

universe u v w

section Components

open CategoryTheory.SimplicialSites

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

variable
    (K0 : DerivedCategory (Sheaf (J ⦋0⦌).toGrothendieck AddCommGrpCat.{w}))
    (α : ((abelianInverseImageExact C J (SimplexCategory.δ (1 : Fin 2))).obj).mapDerivedCategory.obj K0 ≅
      ((abelianInverseImageExact C J (SimplexCategory.δ (0 : Fin 2))).obj).mapDerivedCategory.obj K0)
    (h : CategoryTheory.SimplicialSites.DerivedSystem.cocycleLeft (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ (abelianInverseImageExact C J φ).obj) (AbelianDerived.inverseImageCompIso C J) α =
      CategoryTheory.SimplicialSites.DerivedSystem.cocycleRight (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ (abelianInverseImageExact C J φ).obj) (AbelianDerived.inverseImageCompIso C J) α)

/- Lemma 85.13.3: a coface cocycle determines the last-vertex derived system
on component sites. -/
@[stacks 0GME] #check (CategoryTheory.SimplicialSites.ofCocycleOnComponents C J K0 α h :
    CategoryTheory.SimplicialSites.DerivedSystem (fun n ↦ (J n).toGrothendieck)
      (fun φ ↦ (abelianInverseImageExact C J φ).obj) (AbelianDerived.inverseImageCompIso C J))

/- Lemma 85.13.3: the last-vertex derived system on component sites is cartesian. -/
@[stacks 0GME] #check (CategoryTheory.SimplicialSites.ofCocycleOnComponents_isCartesian C J K0 α h :
    CategoryTheory.SimplicialSites.DerivedSystem.IsCartesian (CategoryTheory.SimplicialSites.ofCocycleOnComponents C J K0 α h))

end Components

section Fibers

open CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

variable
    (K0 : DerivedCategory (Sheaf (J (op ⦋0⦌)).toGrothendieck AddCommGrpCat.{w}))
    (α : ((abelianInverseImageExact F J (SimplexCategory.δ (1 : Fin 2))).obj).mapDerivedCategory.obj K0 ≅
      ((abelianInverseImageExact F J (SimplexCategory.δ (0 : Fin 2))).obj).mapDerivedCategory.obj K0)
    (h : CategoryTheory.SimplicialSites.DerivedSystem.cocycleLeft (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ (abelianInverseImageExact F J φ).obj) (AbelianDerived.inverseImageCompIso F J) α =
      CategoryTheory.SimplicialSites.DerivedSystem.cocycleRight (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ (abelianInverseImageExact F J φ).obj) (AbelianDerived.inverseImageCompIso F J) α)

/- Lemma 85.13.3: a coface cocycle determines the last-vertex derived system
on fiber sites. -/
@[stacks 0GME] #check (CategoryTheory.Grothendieck.ofCocycle F J K0 α h :
    CategoryTheory.SimplicialSites.DerivedSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ (abelianInverseImageExact F J φ).obj) (AbelianDerived.inverseImageCompIso F J))

/- Lemma 85.13.3: the last-vertex derived system on fiber sites is cartesian. -/
@[stacks 0GME] #check (CategoryTheory.Grothendieck.ofCocycle_isCartesian F J K0 α h :
    CategoryTheory.SimplicialSites.DerivedSystem.IsCartesian (CategoryTheory.Grothendieck.ofCocycle F J K0 α h))

end Fibers
