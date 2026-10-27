/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.AugmentationTopos
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberCartesian

/-! # Cartesian module pullbacks along ringed fiberwise augmentations -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn Simplicial

noncomputable section

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [K.IsSite]
variable [∀ n, (J n).IsSite]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [h_fiberwise : IsFiberwiseSite F J]
variable [h_aug : IsAugmentation F J K u0]
include h_fiberwise
include h_aug


open RingedSite

variable (O : Sheaf (topology F J) RingCat.{w})
variable (O_D : Sheaf K.toGrothendieck RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable (aSharp : O_D ⟶ (IsAugmentation.totalTopos F J K u0).ringDirectImage.obj O)

/-- The ringed fiberwise augmentation with structure map adjoint to `aSharp`. -/
def IsAugmentation.ringedTopos :
    ToposHom (fiberTotalRingedSite F J O) (ofRingSheaf K.toGrothendieck O_D) where
  toTopos := IsAugmentation.totalTopos F J K u0
  structureMap := ((IsAugmentation.totalTopos F J K u0).ringAdjunction.homEquiv O_D O).symm
    aSharp

/-- The ringed fiberwise augmentation has the canonical underlying morphism and recovers `aSharp`. -/
theorem IsAugmentation.ringedTopos_spec :
    (IsAugmentation.ringedTopos F J K u0 O O_D aSharp).toTopos =
        IsAugmentation.totalTopos F J K u0 ∧
      (IsAugmentation.ringedTopos F J K u0 O O_D aSharp).directStructureMap = aSharp := sorry

variable [UnivLE.{max u v, w}]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]

variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (fiberStageMorphism F J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fiberRingedToposMap F J O φ)]

variable [(SheafOfModules.restrictScalars.{w}
    (IsAugmentation.ringedTopos F J K u0 O O_D aSharp).structureMap).IsRightAdjoint]

/-- Module pullback along a ringed fiberwise augmentation is cartesian. -/
theorem modulePullback_isCartesian (M : SheafOfModules.{w} O_D) :
    Module.IsCartesian F J O
      ((IsAugmentation.ringedTopos F J K u0 O O_D aSharp).modulePullback.obj M) := sorry

variable [ToposHom.HasModulePullbackDerived
  (IsAugmentation.ringedTopos F J K u0 O O_D aSharp)]

/-- Unbounded derived module pullback along a ringed fiberwise augmentation is cartesian. -/
theorem modulePullbackDerived_isCartesian
    (dK : Hom.ModuleDerived.{w} (ofRingSheaf K.toGrothendieck O_D)) :
    ModuleDerived.IsCartesian F J O
      ((IsAugmentation.ringedTopos F J K u0 O O_D aSharp).modulePullbackDerived.obj dK) := sorry

end CategoryTheory.Grothendieck
