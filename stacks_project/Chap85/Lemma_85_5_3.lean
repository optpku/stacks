/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialDerivedMorphism
public import ReasLib.CategoryTheory.Sites.Simplicial.DerivedMorphism
import StacksCheckRecall

/-!
# Lemma 85.5.3

In the setup of Lemma 85.5.2, restriction along `g_n` commutes with unbounded
derived direct image of abelian sheaves: `(g'_n)⁻¹ ∘ R h_total,* K = R h_n,* ∘ g_n⁻¹ K`
for `K` in `D(Ab(C_total))`. The same identity holds in Situation 85.3.3 case A
(morphisms of sites) and case B (cocontinuous functors).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SimplicialSites

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instC : IsMorphismDiagram C J] [instC' : IsMorphismDiagram C' J']
variable (α : C' ⟶ C)
variable [∀ n (P : (C'.obj n)ᵒᵖ ⥤ Type w), ((α.app n).toFunctor).op.HasLeftKanExtension P]
variable [hα : IsMorphism J J' α]

variable [HasWeakSheafify (topology C J) (Type w)]
variable [HasWeakSheafify (topology C' J') (Type w)]
variable [HasSheafify (topology C J) (Type w)]
variable [HasSheafify (topology C' J') (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasPointwiseRightKanExtension P]
variable [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, ((IsMorphism.totalFunctor α).op).HasLeftKanExtension P]

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C' J') AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J' n).toGrothendieck AddCommGrpCat.{w}]
variable [HasDerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [HasDerivedCategory (Sheaf (topology C' J') AddCommGrpCat.{w})]
variable [∀ n, HasDerivedCategory (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w})]
variable [∀ n, HasDerivedCategory (Sheaf ((J' n).toGrothendieck) AddCommGrpCat.{w})]
variable [IsGrothendieckAbelian.{max u v} (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [∀ n, IsGrothendieckAbelian.{max u v}
    (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w})]

variable (n : SimplexCategory)

/- Lemma 85.5.3 (1)
In Situation 85.3.3 case A, with notation as in Lemma 85.5.2, for
`K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat)` one has
`(g'_n)⁻¹ (R h_total,* K) = R h_n,* (g_n⁻¹ K)` in `D(Ab(C'_n))`. -/
@[stacks 0D97] #check (CategoryTheory.SimplicialSites.IsMorphism.restrict_derivedPushforward J J' α n :
    CategoryTheory.SimplicialSites.IsMorphism.derivedTotal J J' α ⋙
        CategoryTheory.SimplicialSites.derivedRestrict C' J' n ≅
      CategoryTheory.SimplicialSites.derivedRestrict C J n ⋙
        CategoryTheory.SimplicialSites.IsMorphism.derivedPushforward J J' α n)

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [instF : IsFiberwiseSite F J] [instF' : IsFiberwiseSite F' J']
variable (α : F ⟶ F')
variable [hα : IsFiberwiseMorphism J J' α]

variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F' J') (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasWeakSheafify (topology F' J') (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w, (ι F' (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w, (ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ Type w),
    ((α.app n).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
    (Grothendieck.map α).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    ((α.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n) ⋙ Grothendieck.map α).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]

variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F' J') AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J' n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((α.app n).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (Grothendieck.map α).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    ((α.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n) ⋙ Grothendieck.map α).op.HasPointwiseRightKanExtension P]
variable [HasDerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [HasDerivedCategory (Sheaf (topology F' J') AddCommGrpCat.{w})]
variable [∀ n, HasDerivedCategory (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w})]
variable [∀ n, HasDerivedCategory (Sheaf ((J' (op n)).toGrothendieck) AddCommGrpCat.{w})]
variable [IsGrothendieckAbelian.{max u v} (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [∀ n, IsGrothendieckAbelian.{max u v}
    (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w})]

variable (n : SimplexCategory)

/- Lemma 85.5.3 (2)
In Situation 85.3.3 case B, with notation as in Lemma 85.5.2, for
`K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat)` one has
`(g'_n)⁻¹ (R h_total,* K) = R h_n,* (g_n⁻¹ K)` in `D(Ab(C'_n))`. -/
@[stacks 0D97] #check (CategoryTheory.Grothendieck.IsFiberwiseMorphism.restrict_derivedPushforward J J' α n :
    CategoryTheory.Grothendieck.IsFiberwiseMorphism.derivedTotal J J' α ⋙
        CategoryTheory.Grothendieck.derivedRestrict F' J' n ≅
      CategoryTheory.Grothendieck.derivedRestrict F J n ⋙
        CategoryTheory.Grothendieck.IsFiberwiseMorphism.derivedPushforward J J' α n)

end CategoryTheory.Grothendieck

