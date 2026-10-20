/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.SheafComparison
public import ReasLib.CategoryTheory.Sites.Grothendieck.SheafComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe u v w

/- Lemma 85.3.4. Sheaves on the total site are equivalent to systems of stage sheaves
with compatible pushforward transitions. The covariant presentation is checked first. -/
@[stacks 09WF] #check (CategoryTheory.SimplicialSites.sheafEquivalence :
  ∀ (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
  [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
  [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
      ((C.map φ).toFunctor).op.HasLeftKanExtension P]
  [CategoryTheory.SimplicialSites.IsMorphismDiagram C J],
    Sheaf (CategoryTheory.SimplicialSites.topology C J) (Type w) ≌
      CategoryTheory.SimplicialSites.SheafSystem (fun n ↦ (J n).toGrothendieck)
      (fun φ ↦ CategoryTheory.SimplicialSites.toposMap C J φ))

/- Lemma 85.3.4. The fiberwise presentation gives the same description by stage topoi
and their morphisms. -/
@[stacks 09WF] #check (CategoryTheory.Grothendieck.sheafEquivalence :
  ∀ (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
  [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
  [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
      ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
  [CategoryTheory.Grothendieck.IsFiberwiseSite F J],
    Sheaf (CategoryTheory.Grothendieck.topology F J) (Type w) ≌
      CategoryTheory.SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ CategoryTheory.Grothendieck.toposMap F J φ))
