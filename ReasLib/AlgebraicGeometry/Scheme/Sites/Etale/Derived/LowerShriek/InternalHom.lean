/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Pushforward.Compactification
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Presentation
public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open RightDerived.Cochain
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Λ : Type u} [CommRing Λ]

  {Y : Scheme.{u}} (X : Over Y)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  (P : Compactification.Of Y X)
  [sX : HasSheafify (smallEtaleTopology X.left) (ModuleCat.{u} Λ)]
  [∀ U : X.left.Etale,
  HasWeakSheafify ((smallEtaleTopology X.left).over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))]
  [sP : HasSheafify (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)]
  [∀ U : (Over.left P.obj.right).Etale,
  HasWeakSheafify ((smallEtaleTopology (Over.left P.obj.right)).over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))]
  [sY : HasSheafify (smallEtaleTopology Y) (ModuleCat.{u} Λ)]
  [∀ U : Y.Etale,
  HasWeakSheafify ((smallEtaleTopology Y).over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
  [((@etaleExtensionByZero _ _ (Compactification.Of.ι P) inferInstance
    (ModuleCat.{u} Λ) inferInstance inferInstance sP.isRightAdjoint)).Additive]
  [PreservesFiniteLimits
  ((@etaleExtensionByZero _ _ (Compactification.Of.ι P) inferInstance
    (ModuleCat.{u} Λ) inferInstance inferInstance sP.isRightAdjoint))]
  [PreservesFiniteColimits
  ((@etaleExtensionByZero _ _ (Compactification.Of.ι P) inferInstance
    (ModuleCat.{u} Λ) inferInstance inferInstance sP.isRightAdjoint))]
  [aP : (etaleModulePushforward (Over.hom P.obj.right) Λ).Additive]
  [HasRightDerivedFunctor
  (@RightDerived.Cochain.toDerived
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance inferInstance
    ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (smallEtaleTopology Y)
      (smallEtaleTopology (Over.left P.obj.right))) aP)
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [aX : (etaleModulePushforward X.hom Λ).Additive]
  [HasRightDerivedFunctor
  (@RightDerived.Cochain.toDerived
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance inferInstance
    ((smallEtalePullback X.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology X.left)) aX)
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [(etaleRestrictionSheaf (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
  [aJ : (etaleModulePushforward (Compactification.Of.ι P) Λ).Additive]
  [PreservesFiniteLimits
  (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)))]
  [(etaleModulePushforward
    (Compactification.Of.ι P ≫ Over.hom P.obj.right) Λ).Additive]
  [aComp : (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)) ⋙
    ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right)))).Additive]
  [HasRightDerivedFunctor
  (@RightDerived.Cochain.toDerived
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left)) ⋙
      ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology (Over.left P.obj.right)))) aComp)
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (@RightDerived.Cochain.toDerived
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (((smallEtalePullback (Compactification.Of.ι P)).sheafPushforwardContinuous (ModuleCat.{u} Λ) (smallEtaleTopology (Over.left P.obj.right)) (smallEtaleTopology X.left))) aJ)
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

section Normalized

variable [rp : (etaleModulePushforward (Over.hom P.obj.right) Λ).IsRightAdjoint]
  [(@etaleModuleInverseImage Λ inferInstance _ _ (Over.hom P.obj.right) rp).Additive]
  [PreservesFiniteLimits (@etaleModuleInverseImage Λ inferInstance _ _ (Over.hom P.obj.right) rp)]
  [PreservesFiniteColimits (@etaleModuleInverseImage Λ inferInstance _ _ (Over.hom P.obj.right) rp)]

  [mX : MonoidalCategory (DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))]
  [MonoidalClosed (DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))]
  [mP : MonoidalCategory (DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)))]
  [MonoidalClosed (DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)))]
  [mY : MonoidalCategory (DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)))]
  [MonoidalClosed (DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)))]
  [((smallEtaleTopology X.left).W (A := ModuleCat.{u} Λ)).IsMonoidal]
  [@MonoidalPreadditive (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)]
  [∀ A B : GradedObject ℤ (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)),
  @GradedObject.HasTensor ℤ inferInstance _ inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance) A B]
  [∀ A B C : GradedObject ℤ (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)),
  @GradedObject.HasGoodTensor₁₂Tensor ℤ inferInstance _ inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance) A B C]
  [∀ A B C : GradedObject ℤ (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)),
  @GradedObject.HasGoodTensorTensor₂₃ ℤ inferInstance _ inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance) A B C]
  [∀ A B C D : GradedObject ℤ (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)),
  @GradedObject.HasTensor₄ObjExt ℤ inferInstance _ inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance) A B C D]
  [@DerivedCategory.DerivedTensor.Bifunctor.Has (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance]
  [((smallEtaleTopology (Over.left P.obj.right)).W (A := ModuleCat.{u} Λ)).IsMonoidal]
  [@MonoidalPreadditive (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
    inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)]
  [∀ A B : GradedObject ℤ (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)),
  @GradedObject.HasTensor ℤ inferInstance _ inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance) A B]
  [∀ A B C : GradedObject ℤ (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)),
  @GradedObject.HasGoodTensor₁₂Tensor ℤ inferInstance _ inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance) A B C]
  [∀ A B C : GradedObject ℤ (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)),
  @GradedObject.HasGoodTensorTensor₂₃ ℤ inferInstance _ inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance) A B C]
  [∀ A B C D : GradedObject ℤ (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)),
  @GradedObject.HasTensor₄ObjExt ℤ inferInstance _ inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance) A B C D]
  [@DerivedCategory.DerivedTensor.Bifunctor.Has (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance]
  [((smallEtaleTopology Y).W (A := ModuleCat.{u} Λ)).IsMonoidal]
  [@MonoidalPreadditive (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))
    inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance)]
  [∀ A B : GradedObject ℤ (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)),
  @GradedObject.HasTensor ℤ inferInstance _ inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance) A B]
  [∀ A B C : GradedObject ℤ (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)),
  @GradedObject.HasGoodTensor₁₂Tensor ℤ inferInstance _ inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance) A B C]
  [∀ A B C : GradedObject ℤ (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)),
  @GradedObject.HasGoodTensorTensor₂₃ ℤ inferInstance _ inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance) A B C]
  [∀ A B C D : GradedObject ℤ (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)),
  @GradedObject.HasTensor₄ObjExt ℤ inferInstance _ inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance) A B C D]
  [@DerivedCategory.DerivedTensor.Bifunctor.Has (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance]
  [@Functor.Monoidal _ inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance)
    _ inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance) (@etaleModuleInverseImage Λ inferInstance _ _ (Over.hom P.obj.right) rp)]
  [@Functor.Monoidal _ inferInstance mY _ inferInstance mP
    (@etaleModuleInverseImage Λ inferInstance _ _ (Over.hom P.obj.right) rp).mapDerivedCategory]
  [@Functor.Cochain.HasMappedTensorTotals
    (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance)
    inferInstance (@etaleModuleInverseImage Λ inferInstance _ _ (Over.hom P.obj.right) rp) inferInstance]
  [@Functor.Monoidal _ inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
    _ inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance) (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
  [@Functor.Monoidal _ inferInstance mP _ inferInstance mX
    (etaleDerivedRestriction (Compactification.Of.ι P) Λ)]
  [@Functor.Cochain.HasMappedTensorTotals
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
    inferInstance (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ)) inferInstance]




set_option maxHeartbeats 2000000 in
/-- The canonical mixed projection-formula map, the mate of the unit and the tensor map of
restriction. Its normalization is fixed by the tensor-pullback predicate, rather than an independent oplax
structure on extension by zero. -/
def etaleDerivedInteriorProjectionFormula
    (A : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) (C : DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))) :
    (etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj
        (A ⊗ (etaleDerivedRestriction (Compactification.Of.ι P) Λ).obj C) ⟶
      (etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj A ⊗ C :=
  ((etaleDerivedExtensionByZeroAdjunction (Compactification.Of.ι P) Λ).homEquiv
    (A ⊗ (etaleDerivedRestriction (Compactification.Of.ι P) Λ).obj C)
    ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj A ⊗ C)).symm
    (((etaleDerivedExtensionByZeroAdjunction (Compactification.Of.ι P) Λ).unit.app A ⊗ₘ
        𝟙 ((etaleDerivedRestriction (Compactification.Of.ι P) Λ).obj C)) ≫
      (Monoidal.μIso (etaleDerivedRestriction (Compactification.Of.ι P) Λ)
        ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj A) C).hom)

set_option maxHeartbeats 2000000 in
/-- The canonical mixed projection morphism is invertible for normalized tensor presentations. -/
theorem etaleDerivedInteriorProjectionFormula_isIso
    [∀ K L : CochainComplex
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) ℤ,
  IsIso (@Functor.Cochain.tensorComparison
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance) (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
    inferInstance inferInstance (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ)) inferInstance inferInstance K L
    inferInstance inferInstance inferInstance)]
  (TX : tensor (DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) ≅ (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
  (TP : tensor (DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))) ≅
    (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
    (hj : @DerivedCategory.DerivedTensor.Presentation.Pullback
      (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mP
      (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mX (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      TP TX
      (modulePullbackTensor (Compactification.Of.ι P)
        (etaleInteriorSheafPushforwardAdjunction X P)))
    (A : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) (C : DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))) :
    IsIso (etaleDerivedInteriorProjectionFormula X P A C) := sorry

set_option maxHeartbeats 2000000 in
/-- Uncurried evaluation of `j_!` of internal Hom after the mixed projection
formula `j_! A ⊗ Rj_* I ⟶ j_!(A ⊗ j⁻¹ Rj_* I)`. -/
def etaleDerivedInteriorInternalHomEval
    [∀ K L : CochainComplex
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) ℤ,
  IsIso (@Functor.Cochain.tensorComparison
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance) (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
    inferInstance inferInstance (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ)) inferInstance inferInstance K L
    inferInstance inferInstance inferInstance)]
  (TX : tensor (DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) ≅ (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
  (TP : tensor (DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))) ≅
    (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
    (hj : @DerivedCategory.DerivedTensor.Presentation.Pullback
      (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mP
      (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mX (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      TP TX
      (modulePullbackTensor (Compactification.Of.ι P)
        (etaleInteriorSheafPushforwardAdjunction X P)))
    (A B : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) :
    (etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj A ⊗
      (etaleDerivedInteriorPushforward X P).obj ((ihom A).obj B) ⟶
    (etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj B :=
  @CategoryTheory.inv _ _ _ _
    (etaleDerivedInteriorProjectionFormula X P A
      ((etaleDerivedInteriorPushforward X P).obj ((ihom A).obj B)))
    (etaleDerivedInteriorProjectionFormula_isIso X P TX TP hj A
      ((etaleDerivedInteriorPushforward X P).obj ((ihom A).obj B))) ≫
    (etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).map
      ((𝟙 A ⊗ₘ (etaleDerivedInteriorPushforwardAdjunction X P).counit.app
          ((ihom A).obj B)) ≫
        (ihom.ev A).app B)

set_option maxHeartbeats 2000000 in
/-- The interior internal-Hom comparison
`Rj_* RHom(A, B) ⟶ RHom(j_! A, j_! B)`. -/
def etaleDerivedInteriorInternalHom
    [∀ K L : CochainComplex
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) ℤ,
  IsIso (@Functor.Cochain.tensorComparison
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance) (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
    inferInstance inferInstance (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ)) inferInstance inferInstance K L
    inferInstance inferInstance inferInstance)]
  (TX : tensor (DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) ≅ (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
  (TP : tensor (DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))) ≅
    (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
    (hj : @DerivedCategory.DerivedTensor.Presentation.Pullback
      (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mP
      (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mX (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      TP TX
      (modulePullbackTensor (Compactification.Of.ι P)
        (etaleInteriorSheafPushforwardAdjunction X P)))
    (A B : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) :
    (etaleDerivedInteriorPushforward X P).obj ((ihom A).obj B) ⟶
      (ihom ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj A)).obj
        ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj B) :=
  MonoidalClosed.curry
    (A := (etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj A)
    (Y := (etaleDerivedInteriorPushforward X P).obj ((ihom A).obj B))
    (X := (etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj B)
    (etaleDerivedInteriorInternalHomEval X P TX TP hj A B)

set_option maxHeartbeats 2000000 in
/-- For a separated finite-type morphism `f : X ⟶ Y` of
quasi-compact quasi-separated schemes, a torsion coefficient ring `Λ`, and
objects `K`, `L` of `D(X_étale, Λ)`, there is a canonical map
`α : Rf_* RHom_Λ(K, L) ⟶ RHom_Λ(Rf_! K, Rf_! L)`, functorial in `K` and `L`,
obtained from a compactification `f = f̄ ∘ j` as
`α = γ ∘ R f̄_* β` after Leray `Rf_* = R f̄_* ∘ Rj_*`. -/
def etaleDerivedLowerShriekInternalHomOfTensorPresentation
    [∀ K L : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ,
  IsIso (@Functor.Cochain.tensorComparison
    (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance) (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
    inferInstance inferInstance (@etaleModuleInverseImage Λ inferInstance _ _ (Over.hom P.obj.right) rp) inferInstance inferInstance K L
    inferInstance inferInstance inferInstance)]
    [∀ K L : CochainComplex
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) ℤ,
  IsIso (@Functor.Cochain.tensorComparison
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance) (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
    inferInstance inferInstance (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ)) inferInstance inferInstance K L
    inferInstance inferInstance inferInstance)]
    (TX : tensor (DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) ≅ (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
    (TP : tensor (DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))) ≅
      (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
    (TY : tensor (DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))) ≅ (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (hj : @DerivedCategory.DerivedTensor.Presentation.Pullback
      (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mP
      (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mX (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      TP TX
      (modulePullbackTensor (Compactification.Of.ι P)
        (etaleInteriorSheafPushforwardAdjunction X P)))
    (hp : @DerivedCategory.DerivedTensor.Presentation.Pullback
      (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mY
      (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mP (@etaleModuleInverseImage Λ inferInstance _ _ (Over.hom P.obj.right) rp)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      TY TP
      (modulePullbackTensor (Over.hom P.obj.right)
        (@etaleModuleInverseImageAdjunction Λ inferInstance _ _ (Over.hom P.obj.right) rp)))
    (hΛ : AddMonoid.IsTorsion Λ)
    (A B : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) :
    (etaleDerivedPushforward X.hom).obj ((ihom A).obj B) ⟶
      (ihom ((etaleDerivedLowerShriek X P).obj A)).obj
        ((etaleDerivedLowerShriek X P).obj B) :=
  (etaleDerivedPushforwardLeray X P).app ((ihom A).obj B) ≫
    (etaleDerivedPushforward (Over.hom P.obj.right)).map
      (etaleDerivedInteriorInternalHom X P TX TP hj A B) ≫
    @Functor.LaxMonoidal.InternalHom.comparison
      (DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))) _ (DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))) _ _ _
      (etaleDerivedPushforward (Over.hom P.obj.right))
      (etaleDerivedCompactificationPushforwardAdjunction X P).rightAdjointLaxMonoidal
      ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj A)
      ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj B) _ _



set_option maxHeartbeats 2000000 in
/-- The comparison is contravariantly natural in its first argument. -/
theorem etaleDerivedLowerShriekInternalHomOfTensorPresentation_naturality_left
    [∀ K L : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ,
  IsIso (@Functor.Cochain.tensorComparison
    (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance) (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
    inferInstance inferInstance (@etaleModuleInverseImage Λ inferInstance _ _ (Over.hom P.obj.right) rp) inferInstance inferInstance K L
    inferInstance inferInstance inferInstance)]
    [∀ K L : CochainComplex
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) ℤ,
  IsIso (@Functor.Cochain.tensorComparison
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance) (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
    inferInstance inferInstance (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ)) inferInstance inferInstance K L
    inferInstance inferInstance inferInstance)]
  (TX : tensor (DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) ≅ (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
  (TP : tensor (DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))) ≅
    (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
  (TY : tensor (DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))) ≅ (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
  (hj : @DerivedCategory.DerivedTensor.Presentation.Pullback
      (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mP
      (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mX (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      TP TX
    (modulePullbackTensor (Compactification.Of.ι P)
      (etaleInteriorSheafPushforwardAdjunction X P)))
  (hp : @DerivedCategory.DerivedTensor.Presentation.Pullback
      (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mY
      (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mP (@etaleModuleInverseImage Λ inferInstance _ _ (Over.hom P.obj.right) rp)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      TY TP
    (modulePullbackTensor (Over.hom P.obj.right)
      (@etaleModuleInverseImageAdjunction Λ inferInstance _ _ (Over.hom P.obj.right) rp)))
    (hΛ : AddMonoid.IsTorsion Λ)
    {A A' : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))} (a : A' ⟶ A) (B : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) :
    etaleDerivedLowerShriekInternalHomOfTensorPresentation X P TX TP TY hj hp hΛ A B ≫
        (MonoidalClosed.pre ((etaleDerivedLowerShriek X P).map a)).app
          ((etaleDerivedLowerShriek X P).obj B) =
      (etaleDerivedPushforward X.hom).map ((MonoidalClosed.pre a).app B) ≫
        etaleDerivedLowerShriekInternalHomOfTensorPresentation X P TX TP TY hj hp hΛ A' B := sorry

set_option maxHeartbeats 2000000 in
/-- The comparison is covariantly natural in its second argument. -/
theorem etaleDerivedLowerShriekInternalHomOfTensorPresentation_naturality_right
    [∀ K L : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ,
  IsIso (@Functor.Cochain.tensorComparison
    (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance) (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
    inferInstance inferInstance (@etaleModuleInverseImage Λ inferInstance _ _ (Over.hom P.obj.right) rp) inferInstance inferInstance K L
    inferInstance inferInstance inferInstance)]
    [∀ K L : CochainComplex
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) ℤ,
  IsIso (@Functor.Cochain.tensorComparison
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance) (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
    inferInstance inferInstance (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ)) inferInstance inferInstance K L
    inferInstance inferInstance inferInstance)]
  (TX : tensor (DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) ≅ (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
  (TP : tensor (DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))) ≅
    (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
  (TY : tensor (DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))) ≅ (@DerivedCategory.DerivedTensor.Bifunctor.functor (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance))
  (hj : @DerivedCategory.DerivedTensor.Presentation.Pullback
      (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mP
      (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology X.left) Λ
    inferInstance sX.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mX (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      TP TX
    (modulePullbackTensor (Compactification.Of.ι P)
      (etaleInteriorSheafPushforwardAdjunction X P)))
  (hp : @DerivedCategory.DerivedTensor.Presentation.Pullback
      (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology Y) Λ
    inferInstance sY.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mY
      (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) inferInstance inferInstance inferInstance (@Sheaf.moduleSheafMonoidalCategory _ _ (smallEtaleTopology (Over.left P.obj.right)) Λ
    inferInstance sP.isRightAdjoint inferInstance)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance mP (@etaleModuleInverseImage Λ inferInstance _ _ (Over.hom P.obj.right) rp)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      TY TP
    (modulePullbackTensor (Over.hom P.obj.right)
      (@etaleModuleInverseImageAdjunction Λ inferInstance _ _ (Over.hom P.obj.right) rp)))
    (hΛ : AddMonoid.IsTorsion Λ)
    (A : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) {B B' : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))} (b : B ⟶ B') :
    (etaleDerivedPushforward X.hom).map ((ihom A).map b) ≫
        etaleDerivedLowerShriekInternalHomOfTensorPresentation X P TX TP TY hj hp hΛ A B' =
      etaleDerivedLowerShriekInternalHomOfTensorPresentation X P TX TP TY hj hp hΛ A B ≫
        (ihom ((etaleDerivedLowerShriek X P).obj A)).map
          ((etaleDerivedLowerShriek X P).map b) := sorry


end Normalized

section Conditional

variable [mX : MonoidalCategory (DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))]
  [MonoidalClosed (DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))]
  [mP : MonoidalCategory (DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)))]
  [MonoidalClosed (DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)))]
  [mY : MonoidalCategory (DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)))]
  [MonoidalClosed (DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)))]
  [(etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).OplaxMonoidal]
  [(etaleDerivedExtensionByZeroAdjunction
    (Compactification.Of.ι P) Λ).ProjectionFormulaMap]
  [(etaleDerivedPushforward (Over.hom P.obj.right) :
    DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))).LaxMonoidal]

/-- When derived extension by zero satisfies the projection formula and compactification
pushforward is lax monoidal, Leray and evaluation give a comparison
`Rf_* RHom(A, B) ⟶ RHom(Rf_! A, Rf_! B)` for the specified compactification. -/
def etaleDerivedLowerShriekInternalHom (A B : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) :
    (etaleDerivedPushforward X.hom).obj ((ihom A).obj B) ⟶
      (ihom ((etaleDerivedLowerShriek X P).obj A)).obj
        ((etaleDerivedLowerShriek X P).obj B) :=
  (etaleDerivedPushforwardLeray X P).app ((ihom A).obj B) ≫
    (etaleDerivedPushforward (Over.hom P.obj.right)).map
      (MonoidalClosed.curry
        ((etaleDerivedExtensionByZeroAdjunction (Compactification.Of.ι P) Λ).projectionFormulaMapInv A
            ((etaleDerivedInteriorPushforward X P).obj ((ihom A).obj B)) ≫
          (etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).map
            ((𝟙 A ⊗ₘ (etaleDerivedInteriorPushforwardAdjunction X P).counit.app
                ((ihom A).obj B)) ≫
              (ihom.ev A).app B))) ≫
    Functor.LaxMonoidal.InternalHom.comparison
      (etaleDerivedPushforward (Over.hom P.obj.right))
      ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj A)
      ((etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).obj B)

end Conditional

end AlgebraicGeometry.Scheme.Etale

end
