/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Lemma_85_5_2_Fiberwise
public import stacks_project.Chap85.Lemma_85_5_2_Total
import StacksCheckRecall

/-!
# Lemma 85.5.2

A morphism of simplicial sites in Situation 85.3.3 induces a morphism of topoi
of the total sites, commuting with the degree-`n` morphisms `g_n`, and satisfying
the mixed identity `(g'_n)⁻¹ ∘ h_total,* = h_n,* ∘ g_n⁻¹`.
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite
open scoped CategoryTheory.MorphismOfTopoiIn

section Covariant

open CategoryTheory.SimplicialSites

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
include instC instC' hα

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

variable (n : SimplexCategory)

/- Lemma 85.5.2 (1)
In Situation 85.3.3 case A, a morphism of simplicial sites induces a morphism of
topoi `h_total : Sh(C_total) ⟶ Sh(C'_total)` presented by the continuous functor
`v_total = (Grothendieck.map (whiskerRight α Cat.opFunctor)).op`. -/
@[stacks 0D96] #check (CategoryTheory.SimplicialSites.IsMorphism.total J J' α :
  MorphismOfTopoiIn.{u, u, v, v, w} (topology C' J') (topology C J))

/- Lemma 85.5.2 (2)
The degree-`n` square commutes as morphisms of topoi:
`g_n⁻¹ ∘ h_total⁻¹ ≅ h_n⁻¹ ∘ (g'_n)⁻¹`. -/
@[stacks 0D96] #check (CategoryTheory.SimplicialSites.IsMorphism.inverseImage_comp J J' α n :
  (IsMorphism.total J J' α).inverseImage ⋙ (ofStageMorphism C J n).inverseImage ≅
    (ofStageMorphism C' J' n).inverseImage ⋙ (IsMorphism.topos J J' α n).inverseImage)

/- Lemma 85.5.2 (3)
The mixed identity `(g'_n)⁻¹ ∘ h_total,* ≅ h_n,* ∘ g_n⁻¹` in case A. -/
@[stacks 0D96] #check (CategoryTheory.SimplicialSites.IsMorphism.restrict_pushforward J J' α n :
  (IsMorphism.total J J' α).pushforward ⋙ (ofStageMorphism C' J' n).inverseImage ≅
    (ofStageMorphism C J n).inverseImage ⋙ (IsMorphism.topos J J' α n).pushforward)

end Covariant

section Fiberwise

open CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [instF : IsFiberwiseSite F J] [instF' : IsFiberwiseSite F' J']
variable (α : F ⟶ F')
variable [hα : IsFiberwiseMorphism J J' α]
include instF instF' hα

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
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w, (Grothendieck.map α).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    ((α.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n) ⋙ Grothendieck.map α).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]

variable (n : SimplexCategory)

/- Lemma 85.5.2 (4)
In Situation 85.3.3 case B, a morphism of simplicial sites induces a morphism of
topoi `h_total : Sh(C_total) ⟶ Sh(C'_total)` presented by the cocontinuous functor
`v_total = Grothendieck.map α`. -/
@[stacks 0D96] #check (CategoryTheory.Grothendieck.IsFiberwiseMorphism.total J J' α :
  MorphismOfTopoiIn.{u, u, v, v, w} (topology F' J') (topology F J))

/- Lemma 85.5.2 (5)
The degree-`n` square commutes as morphisms of topoi in case B:
`g_n⁻¹ ∘ h_total⁻¹ ≅ h_n⁻¹ ∘ (g'_n)⁻¹`. -/
@[stacks 0D96] #check (CategoryTheory.Grothendieck.IsFiberwiseMorphism.inverseImage_comp J J' α n :
  (IsFiberwiseMorphism.total J J' α).inverseImage ⋙ (fiberMorphism F J n).inverseImage ≅
    (fiberMorphism F' J' n).inverseImage ⋙ (IsFiberwiseMorphism.topos J J' α n).inverseImage)

/- Lemma 85.5.2 (6)
The mixed identity `(g'_n)⁻¹ ∘ h_total,* ≅ h_n,* ∘ g_n⁻¹` in case B. -/
@[stacks 0D96] #check (CategoryTheory.Grothendieck.IsFiberwiseMorphism.restrict_pushforward J J' α n :
  (IsFiberwiseMorphism.total J J' α).pushforward ⋙ (fiberMorphism F' J' n).inverseImage ≅
    (fiberMorphism F J n).inverseImage ⋙ (IsFiberwiseMorphism.topos J J' α n).pushforward)

end Fiberwise
