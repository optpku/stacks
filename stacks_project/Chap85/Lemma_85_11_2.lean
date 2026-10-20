/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.ModuleResolution
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberModuleResolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex Opposite RingedSite
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [h_morphism : IsMorphismDiagram C J]
variable [h_aug : IsAugmentation C J K u0]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf (topology C J) RingCat.{w})
variable (O_D : Sheaf K.toGrothendieck RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (aSharp : O_D ⟶
    (IsAugmentation.totalTopos C J K u0).ringDirectImage.obj O)

variable [(SheafOfModules.restrictScalars.{w} (IsAugmentation.ringedHom C J K u0 O O_D aSharp).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((stageMorphism C J O n).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).structureMap).IsRightAdjoint]
variable (G : SheafOfModules.{w} O_D)

/- Lemma 85.11.2. The exact augmented module complex for a site augmentation. -/
@[stacks 0D7C] #check (CategoryTheory.SimplicialSites.modulePullbackAugmentation_quasiIso C J K u0 O O_D aSharp G :
  QuasiIso
      (modulePullbackAugmentation C J K u0 O O_D aSharp G :
        modulePullbackComplex C J K u0 O O_D aSharp G ⟶
          (ChainComplex.single₀ _).obj ((IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePullback.obj G)))

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [K.IsSite]
variable [∀ n, (J n).IsSite]
variable [h_fiberwise : IsFiberwiseSite F J]
variable [h_aug : IsAugmentation F J K u0]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf (topology F J) RingCat.{w})
variable (O_D : Sheaf K.toGrothendieck RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasSheafify K.toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (aSharp : O_D ⟶
    (IsAugmentation.totalTopos F J K u0).ringDirectImage.obj O)

variable [(SheafOfModules.restrictScalars.{w} (IsAugmentation.ringedHom F J K u0 O O_D aSharp).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((fiberStageMorphism F J O n).comp (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).structureMap).IsRightAdjoint]
variable (G : SheafOfModules.{w} O_D)

/- Lemma 85.11.2. The exact augmented module complex for a site augmentation. -/
@[stacks 0D7C] #check (CategoryTheory.Grothendieck.fiberModulePullbackAugmentation_quasiIso F J K u0 O O_D aSharp G :
  QuasiIso
      (fiberModulePullbackAugmentation F J K u0 O O_D aSharp G :
        fiberModulePullbackComplex F J K u0 O O_D aSharp G ⟶
          (ChainComplex.single₀ _).obj ((IsAugmentation.ringedHom F J K u0 O O_D aSharp).modulePullback.obj G)))

end CategoryTheory.Grothendieck
