/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.SingleSheaf.Flat

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory ComplexShape
open RingedSpace.Module.Derived
open RingedSpace.ModuleDerived
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Kunneth

/-- The canonical comparison from the K-flat derived tensor of two degree-zero module
sheaves to their ordinary tensor product placed in degree zero. -/
noncomputable abbrev singleTensorComparison {P : RingedSpace.{u}}
    [KFlat.HomotopyTensorDescends P]
    [KFlat.TensorDescends P]
    [KFlat.IsLocalization P]
    [HomotopyCategory.KFlat.HasResolutions P.Modules]
    [∀ G₁ G₂ : GradedObject ℤ P.Modules, GradedObject.HasTensor G₁ G₂]
    [∀ G₁ G₂ G₃ : GradedObject ℤ P.Modules,
      GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ : GradedObject ℤ P.Modules,
      GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ P.Modules,
      GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
    (M N : P.Modules) :
    (DerivedCategory.singleFunctor P.Modules 0).obj M ⊗
        (DerivedCategory.singleFunctor P.Modules 0).obj N ⟶
      (DerivedCategory.singleFunctor P.Modules 0).obj (M ⊗ N) :=
  SingleSheaf.tensorComparison M N

/-- The total-left-derived counit comparison from derived pullback of a degree-zero module
sheaf to ordinary pullback placed in degree zero. -/
noncomputable abbrev singlePullbackComparison {P Q : Scheme.{u}} (f : P ⟶ Q)
    (M : Q.Modules) :
    (RingedSpace.modulePullbackDerived f.toShHom).obj
        ((DerivedCategory.singleFunctor Q.Modules 0).obj M) ⟶
      (DerivedCategory.singleFunctor P.Modules 0).obj
        ((Scheme.Modules.pullback f).obj M) :=
  SingleSheaf.pullbackComparison f M

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

variable [KFlat.HomotopyTensorDescends (Limits.pullback a b).toRingedSpace]
variable [KFlat.TensorDescends (Limits.pullback a b).toRingedSpace]
variable [KFlat.IsLocalization (Limits.pullback a b).toRingedSpace]
variable [HomotopyCategory.KFlat.HasResolutions
  (Limits.pullback a b).toRingedSpace.Modules]
variable [∀ G₁ G₂ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ :
  GradedObject ℤ (Limits.pullback a b).toRingedSpace.Modules,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]

/-- The canonical comparison from the derived external tensor product of two degree-zero
module sheaves to their ordinary external tensor product placed in degree zero. -/
noncomputable abbrev singleExternalTensorComparison (F : X.Modules) (G : Y.Modules) :
    ModuleDerived.Kunneth.externalTensorProduct a b
        ((DerivedCategory.singleFunctor X.Modules 0).obj F)
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G) ⟶
      (DerivedCategory.singleFunctor (Limits.pullback a b).Modules 0).obj
        (Scheme.Modules.externalTensorProduct a b F G) :=
  SingleSheaf.externalTensorComparison a b F G

end AlgebraicGeometry.Scheme.Modules.Kunneth

end
