/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Simplicial.Injective
public import ReasLib.CategoryTheory.Sites.Grothendieck.Injective

/-!
# Lemma 85.3.6

In Situation 85.3.3, restriction `F ↦ F_n` along `C_n ⥤ C_total` sends injective
objects of `Ab(C_total)` to injective objects of `Ab(C_n)`, and sends K-injective
cochain complexes in `Ab(C_total)` to K-injective complexes in `Ab(C_n)`.
-/

@[expose] public section

open CategoryTheory ComplexShape Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J] (n : SimplexCategory)
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/- Lemma 85.3.6. Restriction to a component preserves injective abelian sheaves
and K-injective cochain complexes in both presentations of a simplicial site. -/
@[stacks 09WH] #check (CategoryTheory.SimplicialSites.stageRestrict_preservesInjectiveObjects C J n :
  (stageRestrict C J AddCommGrpCat.{w} n).PreservesInjectiveObjects)

#check (CategoryTheory.SimplicialSites.stageRestrict_isKInjective C J n :
  ∀ (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective],
    CochainComplex.IsKInjective
      (((stageRestrict C J AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ)).obj I))

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J] (n : SimplexCategory)
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (J (op n)).toGrothendieck AddCommGrpCat.{w}]

#check (CategoryTheory.Grothendieck.fiberRestrict_preservesInjectiveObjects F J n :
  (fiberRestrict F J AddCommGrpCat.{w} n).PreservesInjectiveObjects)

#check (CategoryTheory.Grothendieck.fiberRestrict_isKInjective F J n :
  ∀ (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective],
    CochainComplex.IsKInjective
      (((fiberRestrict F J AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ)).obj I))

end CategoryTheory.Grothendieck
