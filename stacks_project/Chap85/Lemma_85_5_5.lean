/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.AugmentationCompatibility
public import ReasLib.CategoryTheory.Sites.Simplicial.AugmentationCompatibility
import StacksCheckRecall

/-!
# Lemma 85.5.5

In the data of Remark 85.5.4, the morphisms of topoi `a`, `a'`, `h_total` and
`h₋₁` form a commutative square `Sh(C_total) ⟶ Sh(C'_total)` over
`Sh(D) ⟶ Sh(D')`. Equivalently the inverse images satisfy
`(a')⁻¹ ⋙ h_total⁻¹ ≅ h₋₁⁻¹ ⋙ a⁻¹`. Cases A and B of Situation 85.3.3 are
independent.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn Simplicial

noncomputable section

section

open CategoryTheory.SimplicialSites

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable {D' : Type u} [Category.{v} D'] (K' : Precoverage D')
variable (u0 : D ⥤ C.obj ⦋0⦌) (u0' : D' ⥤ C'.obj ⦋0⦌)
variable (α : C' ⟶ C) (v : D' ⥤ D)
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasWeakSheafify K'.toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [HasWeakSheafify (topology C' J') (Type w)]
variable [HasSheafify (topology C J) (Type w)]
variable [HasSheafify (topology C' J') (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [HasEqualizers (Sheaf K'.toGrothendieck (Type w))]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ P : D'ᵒᵖ ⥤ Type w, u0'.op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : D'ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C' u0' n).op.HasLeftKanExtension P]
variable [∀ n (P : (C'.obj n)ᵒᵖ ⥤ Type w), ((α.app n).toFunctor).op.HasLeftKanExtension P]
variable [∀ P : D'ᵒᵖ ⥤ Type w, v.op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasPointwiseRightKanExtension P]
variable [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, ((IsMorphism.totalFunctor α).op).HasLeftKanExtension P]
variable [instC : IsMorphismDiagram C J] [instC' : IsMorphismDiagram C' J']
variable [hα : IsMorphism J J' α]
variable [h_aug : IsAugmentation C J K u0] [h_aug' : IsAugmentation C' J' K' u0']
variable [h : IsCompatible J J' K K' u0 u0' α v]
include instC instC' hα h_aug h_aug' h

variable [∀ n, (ofStage C n).IsCocontinuous (J n).toGrothendieck (topology C J)]
variable [∀ n, (ofStage C' n).IsCocontinuous (J' n).toGrothendieck (topology C' J')]
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [∀ n, (ofStage C' n).IsContinuous (J' n).toGrothendieck (topology C' J')]

/- Lemma 85.5.5 (1)
The canonical total morphism of augmented simplicial sites commutes with the
canonical augmentations and compatible base morphism on inverse images. -/
@[stacks 0D99] #check
  (CategoryTheory.SimplicialSites.IsCompatible.totalInverseImage_comp J J' K K' u0 u0' α v :
    (IsAugmentation.totalTopos C' J' K' u0')⁻¹ ⋙ (IsMorphism.total J J' α)⁻¹ ≅
      (IsCompatible.topos J J' K K' u0 u0' α v)⁻¹ ⋙
        (IsAugmentation.totalTopos C J K u0)⁻¹)

end

section

open CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable {D' : Type u} [Category.{v} D'] (K' : Precoverage D')
variable (u0 : F.obj (op ⦋0⦌) ⥤ D) (u0' : F'.obj (op ⦋0⦌) ⥤ D')
variable (α : F ⟶ F') (v : D ⥤ D')
variable [instF : IsFiberwiseSite F J] [instF' : IsFiberwiseSite F' J']
variable [hα : IsFiberwiseMorphism J J' α]
variable [h_aug : IsAugmentation F J K u0] [h_aug' : IsAugmentation F' J' K' u0']
variable [h : IsCompatible J J' K K' u0 u0' α v]
include instF instF' hα h_aug h_aug' h
variable [K.IsSite] [K'.IsSite]
variable [∀ n, (J n).IsSite] [∀ n, (J' n).IsSite]
variable [(J (op ⦋0⦌)).IsSite] [(J' (op ⦋0⦌)).IsSite]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasSheafify K.toGrothendieck (Type w)]
variable [HasSheafify K'.toGrothendieck (Type w)]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasWeakSheafify K'.toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F' J') (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasWeakSheafify (topology F' J') (Type w)]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [HasEqualizers (Sheaf K'.toGrothendieck (Type w))]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [∀ (n : SimplexCategory) (P : (F'.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F' u0' n).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F'.obj (op n))ᵒᵖ ⥤ Type w),
    ((F'.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w, (ι F' (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ Type w),
    ((α.app n).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
    (Grothendieck.map α).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    ((α.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n) ⋙ Grothendieck.map α).op.HasPointwiseRightKanExtension P]
variable [∀ P : (F.obj (op ⦋0⦌))ᵒᵖ ⥤ Type w, u0.op.HasPointwiseRightKanExtension P]
variable [∀ P : (F'.obj (op ⦋0⦌))ᵒᵖ ⥤ Type w, u0'.op.HasPointwiseRightKanExtension P]
variable [∀ P : Dᵒᵖ ⥤ Type w, v.op.HasPointwiseRightKanExtension P]
variable [∀ P : (F.obj (op ⦋0⦌))ᵒᵖ ⥤ Type w, (u0 ⋙ v).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor ⋙ (α.app (op m)).toFunctor).op.HasPointwiseRightKanExtension P]

variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, (ι F' (op n)).IsCocontinuous (J' (op n)).toGrothendieck (topology F' J')]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, (ι F' (op n)).IsContinuous (J' (op n)).toGrothendieck (topology F' J')]

/- Lemma 85.5.5 (2)
The canonical total morphism of augmented simplicial sites commutes with the
canonical augmentations and compatible base morphism on inverse images. -/
@[stacks 0D99] #check
  (CategoryTheory.Grothendieck.IsCompatible.totalInverseImage_comp J J' K K' u0 u0' α v :
    (IsAugmentation.totalTopos F' J' K' u0')⁻¹ ⋙
        (IsFiberwiseMorphism.total J J' α)⁻¹ ≅
      (IsCompatible.topos J J' K K' u0 u0' α v)⁻¹ ⋙
        (IsAugmentation.totalTopos F J K u0)⁻¹)

end

