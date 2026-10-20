/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import stacks_project.Chap85.Lemma_85_5_2_Fiberwise
public import stacks_project.Chap85.Lemma_85_6_1_Fiber
public import stacks_project.Chap85.Remark_85_7_1_Fiberwise

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Morphism

/-!
# Component ringed morphism compatibility checks
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped MorphismOfTopoiIn

noncomputable section

namespace CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [IsFiberwiseSite F J] [IsFiberwiseSite F' J']
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F' J') (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasWeakSheafify (topology F' J') (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable (O : Sheaf (topology F J) RingCat.{w})
variable (O' : Sheaf (topology F' J') RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F' J').HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J' n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F' (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F'.obj (op n))ᵒᵖ ⥤ Type w),
    ((F'.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

namespace RingedMorphism

variable {J J' O O'}
variable (f : RingedMorphism J J' O O')
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ Type w),
    ((f.toSimplicial.app n).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
    (Grothendieck.map f.toSimplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    ((f.toSimplicial.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n) ⋙ Grothendieck.map f.toSimplicial).op.HasPointwiseRightKanExtension P]
/- Lemma 85.7.2
Canonical shared mathematical interface. -/
#check (CategoryTheory.Grothendieck.RingedMorphism.topos f :
    ∀ (n : SimplexCategory),
    ToposHom (fiberComponentRingedSite F J O n) (fiberComponentRingedSite F' J' O' n))

#check (CategoryTheory.Grothendieck.RingedMorphism.inverseImage_comp f :
    ∀ (n : SimplexCategory),
    (IsFiberwiseMorphism.total J J' f.toSimplicial).ringInverseImage ⋙
        (fiberMorphism F J n).ringInverseImage ≅
      (fiberMorphism F' J' n).ringInverseImage ⋙
        (IsFiberwiseMorphism.topos J J' f.toSimplicial n).ringInverseImage)

#check (CategoryTheory.Grothendieck.RingedMorphism.inverseImage_comp_structureMap f :
    ∀ (n : SimplexCategory),
    (fiberMorphism F J n).ringInverseImage.map f.structureMap ≫
        (Cocontinuous.structureMapIso
        (X := fiberComponentRingedSite F J O n) (Y := fiberTotalRingedSite F J O)
        (ι F (op n)) (Iso.refl _)).hom =
      (inverseImage_comp f n).hom.app O' ≫
        (IsFiberwiseMorphism.topos J J' f.toSimplicial n).ringInverseImage.map (Cocontinuous.structureMapIso
        (X := fiberComponentRingedSite F' J' O' n) (Y := fiberTotalRingedSite F' J' O')
        (ι F' (op n)) (Iso.refl _)).hom ≫
        (topos f n).structureMap)

variable [UnivLE.{max u v, w}]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F' J' O' n).structureMap).IsRightAdjoint]

#check (CategoryTheory.Grothendieck.RingedMorphism.restrict_modulePushforward f :
    ∀ (n : SimplexCategory),
    (toToposHom f).modulePushforward ⋙ (fiberStageMorphism F' J' O' n).modulePullback ≅
      (fiberStageMorphism F J O n).modulePullback ⋙ (topos f n).modulePushforward)

end RingedMorphism

end CategoryTheory.Grothendieck
