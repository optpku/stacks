/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.ModuleCech
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberModuleCech
public import stacks_project.Chap85.Lemma_85_11_3_Complex
public import stacks_project.Chap85.Lemma_85_11_3_Fiberwise
import StacksCheckRecall


/-!
# Lemma 85.11.3

In Situation 85.3.3, with an augmentation towards a site `D` as in
Remark 85.4.1 and a ring map `O_D ⟶ a_* O`, an `O`-module `F` on `C_total`
determines a canonical complex `0 ⟶ a_* F ⟶ a_{0,*} F_0 ⟶ a_{1,*} F_1 ⟶ ⋯`
of `O_D`-modules, exact in degrees `-1` and `0`. If `F` is injective, the
complex is acyclic and remains acyclic after applying `Hom_{O_D}(G, -)` for
every `O_D`-module `G`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex Opposite RingedSite
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable [UnivLE.{max u v, w}]

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
variable (O : Sheaf (topology C J) RingCat.{w})
variable (O_D : Sheaf K.toGrothendieck RingCat.{w})
variable [(topology C J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasWeakSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (aSharp : O_D ⟶
    (IsAugmentation.totalTopos C J K u0).ringDirectImage.obj O)
variable [(SheafOfModules.restrictScalars.{w}
    (IsAugmentation.ringedHom C J K u0 O O_D aSharp).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((stageMorphism C J O n).comp
      (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).structureMap).IsRightAdjoint]
variable (F : SheafOfModules.{w} O)
include h_morphism
include h_aug

/- Lemma 85.11.3: the canonical augmented cochain is exact in degrees -1 and 0. -/
@[stacks 0D7D] #check (CategoryTheory.SimplicialSites.moduleAugmentationCechCochain_exactAt_negOne_zero C J K u0 O O_D aSharp F :
  ∀ (n : ℤ), n = (-1 : ℤ) ∨ n = (0 : ℤ) →
    (moduleAugmentationCechCochain C J K u0 O O_D aSharp F).ExactAt n)

variable [Injective F]

/- Lemma 85.11.3: the augmented cochain of an injective module is acyclic. -/
@[stacks 0D7D] #check (CategoryTheory.SimplicialSites.moduleAugmentationCechCochain_acyclic_of_injective C J K u0 O O_D aSharp F :
  (moduleAugmentationCechCochain C J K u0 O O_D aSharp F).Acyclic)

/- Lemma 85.11.3: Hom from every target module preserves this acyclicity. -/
@[stacks 0D7D] #check (CategoryTheory.SimplicialSites.homModuleAugmentationCechCochain_acyclic_of_injective C J K u0 O O_D aSharp F :
  ∀ G : SheafOfModules.{w} O_D,
    (homModuleAugmentationCechCochain C J K u0 O O_D aSharp F G).Acyclic)

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable [UnivLE.{max u v, w}]

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [K.IsSite]
variable [∀ n, (J n).IsSite]
variable [h_fiberwise : IsFiberwiseSite F J]
variable [h_aug : IsAugmentation F J K u0]
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
variable [HasWeakSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (aSharp : O_D ⟶
    (IsAugmentation.totalTopos F J K u0).ringDirectImage.obj O)
variable [(SheafOfModules.restrictScalars.{w}
    (IsAugmentation.ringedHom F J K u0 O O_D aSharp).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((fiberStageMorphism F J O n).comp
      (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).structureMap).IsRightAdjoint]
variable (M : SheafOfModules.{w} O)
include h_fiberwise
include h_aug

/- Lemma 85.11.3: the canonical augmented cochain is exact in degrees -1 and 0. -/
@[stacks 0D7D] #check (CategoryTheory.Grothendieck.fiberModuleAugmentationCechCochain_exactAt_negOne_zero F J K u0 O O_D aSharp M :
  ∀ (n : ℤ), n = (-1 : ℤ) ∨ n = (0 : ℤ) →
    (fiberModuleAugmentationCechCochain F J K u0 O O_D aSharp M).ExactAt n)

variable [Injective M]

/- Lemma 85.11.3: the augmented cochain of an injective module is acyclic. -/
@[stacks 0D7D] #check (CategoryTheory.Grothendieck.fiberModuleAugmentationCechCochain_acyclic_of_injective F J K u0 O O_D aSharp M :
  (fiberModuleAugmentationCechCochain F J K u0 O O_D aSharp M).Acyclic)

/- Lemma 85.11.3: Hom from every target module preserves this acyclicity. -/
@[stacks 0D7D] #check (CategoryTheory.Grothendieck.fiberHomModuleAugmentationCechCochain_acyclic_of_injective F J K u0 O O_D aSharp M :
  ∀ G : SheafOfModules.{w} O_D,
    (fiberHomModuleAugmentationCechCochain F J K u0 O O_D aSharp M G).Acyclic)

end CategoryTheory.Grothendieck
