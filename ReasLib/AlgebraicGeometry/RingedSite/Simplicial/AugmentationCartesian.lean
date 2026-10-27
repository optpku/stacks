/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.AugmentationTopos
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Cartesian

/-! # Cartesian module pullbacks along ringed simplicial augmentations -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram.{u, v, max u v} C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type (max u v))]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type (max u v)),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type (max u v))]
variable [HasWeakSheafify (topology C J) (Type (max u v))]
variable [∀ P : Dᵒᵖ ⥤ Type (max u v), u0.op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type (max u v)),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type (max u v)))]
variable [IsAugmentation.{u, v, max u v} C J K u0]

variable (O : Sheaf (topology C J) RingCat.{max u v})
variable (O_D : Sheaf K.toGrothendieck RingCat.{max u v})
variable [(topology C J).HasSheafCompose (forget RingCat.{max u v})]
variable [K.toGrothendieck.HasSheafCompose (forget RingCat.{max u v})]
variable (aSharp : O_D ⟶ (IsAugmentation.totalTopos C J K u0).ringDirectImage.obj O)

/-- The ringed augmentation whose structure map is the adjoint mate of `aSharp`. -/
def IsAugmentation.ringedTopos :
    ToposHom (totalRingedSite C J O) (ofRingSheaf K.toGrothendieck O_D) where
  toTopos := IsAugmentation.totalTopos C J K u0
  structureMap := ((IsAugmentation.totalTopos C J K u0).ringAdjunction.homEquiv O_D O).symm
    aSharp

/-- The ringed augmentation has the canonical underlying augmentation and recovers `aSharp`. -/
theorem IsAugmentation.ringedTopos_spec :
    (IsAugmentation.ringedTopos C J K u0 O O_D aSharp).toTopos =
        IsAugmentation.totalTopos C J K u0 ∧
      (IsAugmentation.ringedTopos C J K u0 O O_D aSharp).directStructureMap = aSharp := sorry

variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{max u v})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type (max u v))]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type (max u v),
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{max u v}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{max u v}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]
variable [(SheafOfModules.restrictScalars.{max u v}
    (IsAugmentation.ringedTopos C J K u0 O O_D aSharp).structureMap).IsRightAdjoint]

/-- Module pullback along the ringed augmentation is cartesian. -/
theorem modulePullback_isCartesian (M : SheafOfModules.{max u v} O_D) :
    Module.IsCartesian C J O
      ((IsAugmentation.ringedTopos C J K u0 O O_D aSharp).modulePullback.obj M) := sorry

variable [ToposHom.HasModulePullbackDerived
  (IsAugmentation.ringedTopos C J K u0 O O_D aSharp)]

/-- Unbounded derived module pullback along the ringed augmentation is cartesian. -/
theorem modulePullbackDerived_isCartesian
    (dK : Hom.ModuleDerived.{max u v} (ofRingSheaf K.toGrothendieck O_D)) :
    ModuleDerived.IsCartesian C J O
      ((IsAugmentation.ringedTopos C J K u0 O O_D aSharp).modulePullbackDerived.obj dK) := sorry

end CategoryTheory.SimplicialSites
