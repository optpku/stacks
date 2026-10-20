module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.SheafyTrace
import StacksCheckRecall

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




variable [((etaleDerivedLowerShriek X P :
    DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)))).IsLeftAdjoint]

variable
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

variable
    (L : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))
    (K : DerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)))

set_option maxHeartbeats 2000000 in
/- 63.11.4.1: for a separated finite-type morphism `f : X ⟶ Y` of
quasi-compact quasi-separated schemes and a torsion coefficient ring `Λ`,
and for `L` in `D(X_étale, Λ)` and `K` in `D(Y_étale, Λ)`, there is a
canonical sheafy-trace morphism
`Rf_* RHom_Λ(L, Rf^! K) ⟶ RHom_Λ(Rf_! L, K)`, the Remark 63.10.9
internal-Hom comparison `α` at `(L, Rf^! K)` followed by
`RHom(Rf_! L, ε_K)` for the counit `ε` of `Rf_! ⊣ Rf^!`. -/
@[stacks 0GLB] #check (AlgebraicGeometry.Scheme.Etale.etaleDerivedSheafyTraceOfTensorPresentation
    X P TX TP TY hj hp hΛ L K :
    (etaleDerivedPushforward X.hom).obj
      ((ihom L).obj ((etaleDerivedUpperShriek X Λ P).obj K)) ⟶
    (ihom ((etaleDerivedLowerShriek X P).obj L)).obj K)

end Normalized

end AlgebraicGeometry.Scheme.Etale

end
