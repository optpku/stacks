/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Simplicial.CartesianDescent
public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialDescent

/-! Cartesian sheaves and coface descent in both presentations of a simplicial site. -/

@[expose] public section

open CategoryTheory Opposite

universe u v w

section MorphismDiagram

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    (C.map φ).toFunctor.op.HasLeftKanExtension P]
variable [CategoryTheory.SimplicialSites.IsMorphismDiagram.{u, v, w} C J]

/- Lemma 85.12.4 (1)
Cartesian sheaves of sets in the morphism-of-sites presentation are equivalent to degree-zero sheaves equipped
with an invertible coface comparison satisfying the degree-two cocycle. -/
@[stacks 0D7I] #check (CategoryTheory.SimplicialSites.Sheaf.cartesianEquivalence C J (Type w) :
  CategoryTheory.SimplicialSites.Sheaf.Cartesian C J (Type w) ≌
    CategoryTheory.SimplicialSites.Sheaf.FaceDescent C J (Type w))

#check (CategoryTheory.SimplicialSites.Sheaf.cartesianEquivalence_functor C J (Type w) :
  (CategoryTheory.SimplicialSites.Sheaf.cartesianEquivalence C J (Type w)).functor =
    CategoryTheory.SimplicialSites.Sheaf.toDescentFunctor C J (Type w))
#check (CategoryTheory.SimplicialSites.Sheaf.cartesianEquivalence_inverse C J (Type w) :
  (CategoryTheory.SimplicialSites.Sheaf.cartesianEquivalence C J (Type w)).inverse =
    CategoryTheory.SimplicialSites.Sheaf.ofDescentFunctor C J (Type w))

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    (C.map φ).toFunctor.op.HasLeftKanExtension P]

/- Lemma 85.12.4 (2)
Cartesian sheaves of abelian groups in the morphism-of-sites presentation are equivalent to degree-zero sheaves equipped
with an invertible coface comparison satisfying the degree-two cocycle. -/
@[stacks 0D7I] #check (CategoryTheory.SimplicialSites.Sheaf.cartesianEquivalence C J AddCommGrpCat.{w} :
  CategoryTheory.SimplicialSites.Sheaf.Cartesian C J AddCommGrpCat.{w} ≌
    CategoryTheory.SimplicialSites.Sheaf.FaceDescent C J AddCommGrpCat.{w})

#check (CategoryTheory.SimplicialSites.Sheaf.cartesianEquivalence_functor C J AddCommGrpCat.{w} :
  (CategoryTheory.SimplicialSites.Sheaf.cartesianEquivalence C J AddCommGrpCat.{w}).functor =
    CategoryTheory.SimplicialSites.Sheaf.toDescentFunctor C J AddCommGrpCat.{w})
#check (CategoryTheory.SimplicialSites.Sheaf.cartesianEquivalence_inverse C J AddCommGrpCat.{w} :
  (CategoryTheory.SimplicialSites.Sheaf.cartesianEquivalence C J AddCommGrpCat.{w}).inverse =
    CategoryTheory.SimplicialSites.Sheaf.ofDescentFunctor C J AddCommGrpCat.{w})

end MorphismDiagram

section Fiberwise

variable (C : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [CategoryTheory.Grothendieck.IsFiberwiseSite C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (CategoryTheory.Grothendieck.topology C J) (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj (op n))ᵒᵖ ⥤ Type w),
    (C.map φ.op).toFunctor.op.HasPointwiseRightKanExtension P]

/- Lemma 85.12.4 (3)
Cartesian sheaves of sets in the cocontinuous presentation are equivalent to degree-zero sheaves equipped
with an invertible coface comparison satisfying the degree-two cocycle. -/
@[stacks 0D7I] #check (CategoryTheory.Grothendieck.Sheaf.cartesianEquivalence C J (Type w) :
  CategoryTheory.Grothendieck.Sheaf.Cartesian C J (Type w) ≌
    CategoryTheory.Grothendieck.Sheaf.FaceDescent C J (Type w))

#check (CategoryTheory.Grothendieck.Sheaf.cartesianEquivalence_functor C J (Type w) :
  (CategoryTheory.Grothendieck.Sheaf.cartesianEquivalence C J (Type w)).functor =
    CategoryTheory.Grothendieck.Sheaf.toDescentFunctor C J (Type w))
#check (CategoryTheory.Grothendieck.Sheaf.cartesianEquivalence_inverse C J (Type w) :
  (CategoryTheory.Grothendieck.Sheaf.cartesianEquivalence C J (Type w)).inverse =
    CategoryTheory.Grothendieck.Sheaf.ofDescentFunctor C J (Type w))

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (CategoryTheory.Grothendieck.topology C J) AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n)
    (P : (C.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    (C.map φ.op).toFunctor.op.HasPointwiseRightKanExtension P]

/- Lemma 85.12.4 (4)
Cartesian sheaves of abelian groups in the cocontinuous presentation are equivalent to degree-zero sheaves equipped
with an invertible coface comparison satisfying the degree-two cocycle. -/
@[stacks 0D7I] #check (CategoryTheory.Grothendieck.Sheaf.cartesianEquivalence C J AddCommGrpCat.{w} :
  CategoryTheory.Grothendieck.Sheaf.Cartesian C J AddCommGrpCat.{w} ≌
    CategoryTheory.Grothendieck.Sheaf.FaceDescent C J AddCommGrpCat.{w})

#check (CategoryTheory.Grothendieck.Sheaf.cartesianEquivalence_functor C J AddCommGrpCat.{w} :
  (CategoryTheory.Grothendieck.Sheaf.cartesianEquivalence C J AddCommGrpCat.{w}).functor =
    CategoryTheory.Grothendieck.Sheaf.toDescentFunctor C J AddCommGrpCat.{w})
#check (CategoryTheory.Grothendieck.Sheaf.cartesianEquivalence_inverse C J AddCommGrpCat.{w} :
  (CategoryTheory.Grothendieck.Sheaf.cartesianEquivalence C J AddCommGrpCat.{w}).inverse =
    CategoryTheory.Grothendieck.Sheaf.ofDescentFunctor C J AddCommGrpCat.{w})

end Fiberwise
