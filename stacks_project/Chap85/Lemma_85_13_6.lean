/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.DerivedSystem.Gluing
public import ReasLib.CategoryTheory.Sites.Grothendieck.DerivedSystem.Gluing
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialSites CategoryTheory.Limits Opposite Functor

universe u v w

section CaseA

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

/- Lemma 85.13.6 (1): in case A, compatible maps of restriction systems lift to total
morphisms under the stated shifted Hom vanishing. -/
@[stacks 0D9K] #check
  (CategoryTheory.SimplicialSites.exists_hom_of_toDerivedSystemHom C J :
    ∀ (K K' : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
      [AbelianDerived.IsCartesian C J K],
    (∀ (n : SimplexCategory), 1 < n.len →
      Subsingleton
        (((toDerivedSystem C J K).obj n)⟦(n.len : ℤ) - 1⟧ ⟶ (toDerivedSystem C J K').obj n)) →
    ∀ (α : DerivedSystem.Hom (toDerivedSystem C J K) (toDerivedSystem C J K')),
      ∃ f : K ⟶ K', ∀ n, (toDerivedSystemMap C J f).app n = α.app n)

end CaseA

section CaseB

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [Grothendieck.IsFiberwiseSite F J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (Grothendieck.topology F J) (Type w)]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (Grothendieck.topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/- Lemma 85.13.6 (2): in case B, compatible maps of restriction systems lift to total
morphisms under the stated shifted Hom vanishing. -/
@[stacks 0D9K] #check
  (CategoryTheory.Grothendieck.exists_hom_of_toDerivedSystemHom F J :
    ∀ (K K' : DerivedCategory (Sheaf (Grothendieck.topology F J) AddCommGrpCat.{w}))
      [Grothendieck.AbelianDerived.IsCartesian F J K],
    (∀ (n : SimplexCategory), 1 < n.len →
      Subsingleton
        (((Grothendieck.toDerivedSystem F J K).obj n)⟦(n.len : ℤ) - 1⟧ ⟶
          (Grothendieck.toDerivedSystem F J K').obj n)) →
    ∀ (α : SimplicialSites.DerivedSystem.Hom
      (Grothendieck.toDerivedSystem F J K) (Grothendieck.toDerivedSystem F J K')),
      ∃ f : K ⟶ K', ∀ n, (Grothendieck.derivedRestrict F J n).map f = α.app n)

end CaseB
