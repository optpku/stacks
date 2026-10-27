/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Simplicial.CartesianHom
public import ReasLib.CategoryTheory.Sites.Grothendieck.CartesianHom

/-!
# Lemma 85.13.5

A morphism from a cartesian object of the derived category of the total site
is zero when its degree-zero restriction is zero and the shifted stage Hom
groups vanish, in both presentations of a simplicial site.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram.{u, v, w} C J]
include instMorphismDiagram instWeakSheafify instLeftKan
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

variable (K K' : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
variable [AbelianDerived.IsCartesian C J K]

/- Lemma 85.13.5 (1): zero detection in the covariant presentation. -/
@[stacks 0D9J] #check (CategoryTheory.SimplicialSites.AbelianDerived.hom_eq_zero C J K K' :
  (∀ n : SimplexCategory, 0 < n.len →
    Subsingleton (((derivedRestrict C J n).obj K)⟦(n.len : ℤ)⟧ ⟶
      (derivedRestrict C J n).obj K')) →
  (∀ n : SimplexCategory,
    Subsingleton (((derivedRestrict C J n).obj K)⟦((n.len : ℤ) + 1)⟧ ⟶
      (derivedRestrict C J n).obj K')) →
  ∀ f : K ⟶ K', (derivedRestrict C J ⦋0⦌).map f = 0 → f = 0)

#check (CategoryTheory.SimplicialSites.AbelianDerived.hom_eq_of_eq_component C J K K' :
  (∀ n : SimplexCategory, 0 < n.len →
    Subsingleton (((derivedRestrict C J n).obj K)⟦(n.len : ℤ)⟧ ⟶
      (derivedRestrict C J n).obj K')) →
  (∀ n : SimplexCategory,
    Subsingleton (((derivedRestrict C J n).obj K)⟦((n.len : ℤ) + 1)⟧ ⟶
      (derivedRestrict C J n).obj K')) →
  ∀ f g : K ⟶ K',
    (derivedRestrict C J ⦋0⦌).map f = (derivedRestrict C J ⦋0⦌).map g → f = g)

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable (K K' : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
variable [AbelianDerived.IsCartesian F J K]

/- Lemma 85.13.5 (2): zero detection in the fiberwise presentation. -/
@[stacks 0D9J] #check (CategoryTheory.Grothendieck.AbelianDerived.hom_eq_zero F J K K' :
  (∀ n : SimplexCategory, 0 < n.len →
    Subsingleton (((derivedRestrict F J n).obj K)⟦(n.len : ℤ)⟧ ⟶
      (derivedRestrict F J n).obj K')) →
  (∀ n : SimplexCategory,
    Subsingleton (((derivedRestrict F J n).obj K)⟦((n.len : ℤ) + 1)⟧ ⟶
      (derivedRestrict F J n).obj K')) →
  ∀ f : K ⟶ K', (derivedRestrict F J ⦋0⦌).map f = 0 → f = 0)

end CategoryTheory.Grothendieck
