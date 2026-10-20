/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.UpperShriek
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.InternalHom

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open RightDerived.Cochain
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section Conditional

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of Y X)
variable [HasSheafify (smallEtaleTopology X.left) (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify ((smallEtaleTopology X.left).over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))]
variable [HasSheafify (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)]
variable [∀ U : (Over.left P.obj.right).Etale,
  HasWeakSheafify ((smallEtaleTopology (Over.left P.obj.right)).over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))]
variable [HasSheafify (smallEtaleTopology Y) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify ((smallEtaleTopology Y).over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (smallEtaleTopology Y)
    (smallEtaleTopology (Over.left P.obj.right))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (smallEtaleTopology Y)
      (smallEtaleTopology (Over.left P.obj.right))))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback X.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology X.left)).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback X.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology X.left)))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [(etaleRestrictionSheaf (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [(etaleModulePushforward (Compactification.Of.ι P) Λ).Additive]
variable [PreservesFiniteLimits
  (etaleModulePushforward (Compactification.Of.ι P) Λ)]
variable [PreservesFiniteColimits
  (etaleModulePushforward (Compactification.Of.ι P) Λ)]
variable [(etaleModulePushforward (Compactification.Of.ι P) Λ).PreservesInjectiveObjects]
variable [(ExactFunctor.of
    (etaleModulePushforward (Compactification.Of.ι P) Λ)).obj.PreservesInjectiveObjects]
variable [(etaleModulePushforward (Over.hom P.obj.right) Λ).Additive]
variable [(etaleModulePushforward X.hom Λ).Additive]
variable [(etaleModulePushforward
    (Compactification.Of.ι P ≫ Over.hom P.obj.right) Λ).Additive]
variable [(etaleModulePushforward (Compactification.Of.ι P) Λ ⋙
    etaleModulePushforward (Over.hom P.obj.right) Λ).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (Compactification.Of.ι P) Λ ⋙
      etaleModulePushforward (Over.hom P.obj.right) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [MonoidalCategory (DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))]
variable [MonoidalClosed (DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))]
variable [MonoidalCategory (DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)))]
variable [MonoidalClosed (DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)))]
variable [MonoidalCategory (DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)))]
variable [MonoidalClosed (DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)))]
variable [(etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).OplaxMonoidal]
variable [(etaleDerivedExtensionByZeroAdjunction
    (Compactification.Of.ι P) Λ).ProjectionFormulaMap]
variable [(etaleDerivedPushforward (Over.hom P.obj.right) :
    DerivedCategory (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))).LaxMonoidal]
variable [((etaleDerivedLowerShriek X P :
    DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)))).IsLeftAdjoint]

/-- For the supplied monoidal structures, extension-by-zero oplax structure,
projection-formula map and proper-pushforward lax structure, the conditional
sheafy-trace morphism is the internal-Hom comparison followed by the counit. -/
def etaleDerivedSheafyTrace
    (L : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) (K : DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))) :
    (etaleDerivedPushforward X.hom).obj
      ((ihom L).obj ((etaleDerivedUpperShriek X Λ P).obj K)) ⟶
    (ihom ((etaleDerivedLowerShriek X P).obj L)).obj K :=
  etaleDerivedLowerShriekInternalHom X P L
      ((etaleDerivedUpperShriek X Λ P).obj K) ≫
    (ihom ((etaleDerivedLowerShriek X P).obj L)).map
      ((etaleDerivedLowerShriekAdjunction X Λ P).counit.app K)

/-- The sheafy-trace morphism is the internal-Hom comparison at
`(L, Rf^! K)` followed by the counit of `Rf_! ⊣ Rf^!`. -/
theorem etaleDerivedSheafyTrace_eq
    (L : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) (K : DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))) :
    etaleDerivedSheafyTrace X P L K =
      etaleDerivedLowerShriekInternalHom X P L
          ((etaleDerivedUpperShriek X Λ P).obj K) ≫
        (ihom ((etaleDerivedLowerShriek X P).obj L)).map
          ((etaleDerivedLowerShriekAdjunction X Λ P).counit.app K) :=
  sorry

/-- The sheafy-trace morphism is natural in the source object `L`. -/
theorem etaleDerivedSheafyTrace_natural_left
    {L L' : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))} (f : L ⟶ L') (K : DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))) :
    (etaleDerivedPushforward X.hom).map
          ((MonoidalClosed.pre f).app ((etaleDerivedUpperShriek X Λ P).obj K)) ≫
        etaleDerivedSheafyTrace X P L K =
      etaleDerivedSheafyTrace X P L' K ≫
        (MonoidalClosed.pre ((etaleDerivedLowerShriek X P).map f)).app K :=
  sorry

/-- The sheafy-trace morphism is natural in the target object `K`. -/
theorem etaleDerivedSheafyTrace_natural_right
    (L : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))) {K K' : DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))} (g : K ⟶ K') :
    (etaleDerivedPushforward X.hom).map
          ((ihom L).map ((etaleDerivedUpperShriek X Λ P).map g)) ≫
        etaleDerivedSheafyTrace X P L K' =
      etaleDerivedSheafyTrace X P L K ≫
        (ihom ((etaleDerivedLowerShriek X P).obj L)).map g :=
  sorry

end Conditional

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




variable [((etaleDerivedLowerShriek X P :
    DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)))).IsLeftAdjoint]

set_option maxHeartbeats 2000000 in
/-- For torsion coefficients and tensor presentations normalized along the
compactification pullbacks, the sheafy-trace morphism is the normalized
internal-Hom comparison followed by internal Hom applied to the upper-shriek
adjunction counit. -/
def etaleDerivedSheafyTraceOfTensorPresentation
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
    (L : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))
    (K : DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))) :
    (etaleDerivedPushforward X.hom).obj
      ((ihom L).obj ((etaleDerivedUpperShriek X Λ P).obj K)) ⟶
    (ihom ((etaleDerivedLowerShriek X P).obj L)).obj K :=
  etaleDerivedLowerShriekInternalHomOfTensorPresentation X P TX TP TY hj hp hΛ L
      ((etaleDerivedUpperShriek X Λ P).obj K) ≫
    (ihom ((etaleDerivedLowerShriek X P).obj L)).map
      ((etaleDerivedLowerShriekAdjunction X Λ P).counit.app K)

set_option maxHeartbeats 2000000 in
/-- The tensor-normalized sheafy trace is the internal-Hom comparison at
`(L, Rf^! K)` followed by the morphism induced by the adjunction counit. -/
theorem etaleDerivedSheafyTraceOfTensorPresentation_eq
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
    (L : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))
    (K : DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))) :
    etaleDerivedSheafyTraceOfTensorPresentation X P TX TP TY hj hp hΛ L K =
      etaleDerivedLowerShriekInternalHomOfTensorPresentation X P TX TP TY hj hp hΛ L
          ((etaleDerivedUpperShriek X Λ P).obj K) ≫
        (ihom ((etaleDerivedLowerShriek X P).obj L)).map
          ((etaleDerivedLowerShriekAdjunction X Λ P).counit.app K)
    := rfl

set_option maxHeartbeats 2000000 in
/-- For a separated finite-type morphism between quasi-compact quasi-separated
schemes and torsion coefficients, the tensor-normalized sheafy-trace morphism
is an isomorphism for arbitrary unbounded derived objects. -/
theorem etaleDerivedSheafyTrace_isIso
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
    (L : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))
    (K : DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))) :
    IsIso (etaleDerivedSheafyTraceOfTensorPresentation X P TX TP TY hj hp hΛ L K) :=
  sorry

attribute [instance] etaleDerivedSheafyTrace_isIso

end Normalized

end AlgebraicGeometry.Scheme.Etale

end
