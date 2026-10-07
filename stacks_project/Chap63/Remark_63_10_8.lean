module

public import Mathlib.GroupTheory.Torsion
public import stacks_project.Chap63.Remark_63_10_8_ChangeOfRings
import Mathlib.Tactic.CrossRefAttribute

/-!
# Change of rings for derived étale lower shriek

Restriction of scalars along a homomorphism of torsion rings commutes with
`Rf_!`, as does derived extension of scalars `- ⊗_Λ1^L Λ2`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Etale

variable {Y : Scheme.{u}} (X : Over Y) {Λ1 Λ2 : Type u} [CommRing Λ1] [CommRing Λ2]
variable (φ : Λ1 →+* Λ2)
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of Y X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ1)]
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ2)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ1))]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ2))]
variable [HasSheafify (Over.left P.obj.right).smallEtaleTopology (ModuleCat.{u} Λ1)]
variable [HasSheafify (Over.left P.obj.right).smallEtaleTopology (ModuleCat.{u} Λ2)]
variable [∀ U : (Over.left P.obj.right).Etale,
  HasWeakSheafify ((Over.left P.obj.right).smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
variable [∀ U : (Over.left P.obj.right).Etale,
  HasWeakSheafify ((Over.left P.obj.right).smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
variable [HasDerivedCategory
  (Sheaf (Over.left P.obj.right).smallEtaleTopology (ModuleCat.{u} Λ1))]
variable [HasDerivedCategory
  (Sheaf (Over.left P.obj.right).smallEtaleTopology (ModuleCat.{u} Λ2))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ1)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ2)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ1)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ2)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2))]
variable [X.left.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
variable [(Over.left P.obj.right).smallEtaleTopology.HasSheafCompose
  (ModuleCat.restrictScalars φ)]
variable [Y.smallEtaleTopology.HasSheafCompose (ModuleCat.restrictScalars φ)]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ1,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ2,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(ModuleCat.restrictScalars φ).PreservesLeftKanExtensions
  (etaleRestriction (Compactification.Of.ι P)).op]
variable [(Over.left P.obj.right).smallEtaleTopology.PreservesSheafification
  (ModuleCat.restrictScalars φ)]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ1)).Additive]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ2)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ1))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ1))]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ2))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ2))]
variable [((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ1) Y.smallEtaleTopology
    (Over.left P.obj.right).smallEtaleTopology).Additive]
variable [((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ2) Y.smallEtaleTopology
    (Over.left P.obj.right).smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ1) Y.smallEtaleTopology
      (Over.left P.obj.right).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (Over.left P.obj.right).smallEtaleTopology (ModuleCat.{u} Λ1))
    (up ℤ))]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ2) Y.smallEtaleTopology
      (Over.left P.obj.right).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (Over.left P.obj.right).smallEtaleTopology (ModuleCat.{u} Λ2))
    (up ℤ))]
variable [(Functor.Homotopy.toDerived
    (etaleModuleExtendScalars φ X.left)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]
variable [(Functor.Homotopy.toDerived
    (etaleModuleExtendScalars φ (Over.left P.obj.right))).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (Sheaf (Over.left P.obj.right).smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]
variable [(Functor.Homotopy.toDerived
    (etaleModuleExtendScalars φ Y)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1)) (up ℤ))]

/-- Remark 63.10.8 (1): for a homomorphism `φ : Λ1 →+* Λ2` of torsion rings and a
separated finite-type morphism `f = X.hom` of quasi-compact quasi-separated
schemes, `Rf_!` commutes with restriction of scalars
`D(-, Λ2) ⥤ D(-, Λ1)`. -/
@[stacks 0GL6]
def etaleDerivedLowerShriekRestrictScalarsIso
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2) :
    (etaleDerivedLowerShriek X P ⋙ etaleDerivedRestrictScalars φ Y :
        EtaleDerived X.left Λ2 ⥤ EtaleDerived Y Λ1) ≅
      (etaleDerivedRestrictScalars φ X.left ⋙ etaleDerivedLowerShriek X P) :=
  Functor.associator
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ2)).mapDerivedCategory)
      (etaleDerivedPushforward (Over.hom P.obj.right))
      (etaleDerivedRestrictScalars φ Y) ≪≫
    Functor.isoWhiskerLeft
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ2)).mapDerivedCategory)
      (etaleDerivedRestrictScalars_pushforwardIso φ (Over.hom P.obj.right)) ≪≫
    (Functor.associator
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ2)).mapDerivedCategory)
      (etaleDerivedRestrictScalars φ (Over.left P.obj.right))
      (etaleDerivedPushforward (Over.hom P.obj.right))).symm ≪≫
    Functor.isoWhiskerRight
      (etaleDerivedRestrictScalars_extensionByZeroIso φ
        (Compactification.Of.ι P))
      (etaleDerivedPushforward (Over.hom P.obj.right)) ≪≫
    Functor.associator (etaleDerivedRestrictScalars φ X.left)
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ1)).mapDerivedCategory)
      (etaleDerivedPushforward (Over.hom P.obj.right))

/-- Evaluating the restriction-of-scalars comparison on an object of
`D(X_étale, Λ2)`. -/
theorem etaleDerivedLowerShriekRestrictScalarsIso_hom_app
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2)
    (K : EtaleDerived X.left Λ2) :
    (etaleDerivedLowerShriekRestrictScalarsIso X φ P hΛ1 hΛ2).hom.app K =
      (Functor.associator
          ((etaleExtensionByZero (Compactification.Of.ι P)
              (ModuleCat.{u} Λ2)).mapDerivedCategory)
          (etaleDerivedPushforward (Over.hom P.obj.right))
          (etaleDerivedRestrictScalars φ Y) ≪≫
        Functor.isoWhiskerLeft
          ((etaleExtensionByZero (Compactification.Of.ι P)
              (ModuleCat.{u} Λ2)).mapDerivedCategory)
          (etaleDerivedRestrictScalars_pushforwardIso φ (Over.hom P.obj.right)) ≪≫
        (Functor.associator
          ((etaleExtensionByZero (Compactification.Of.ι P)
              (ModuleCat.{u} Λ2)).mapDerivedCategory)
          (etaleDerivedRestrictScalars φ (Over.left P.obj.right))
          (etaleDerivedPushforward (Over.hom P.obj.right))).symm ≪≫
        Functor.isoWhiskerRight
          (etaleDerivedRestrictScalars_extensionByZeroIso φ
            (Compactification.Of.ι P))
          (etaleDerivedPushforward (Over.hom P.obj.right)) ≪≫
        Functor.associator (etaleDerivedRestrictScalars φ X.left)
          ((etaleExtensionByZero (Compactification.Of.ι P)
              (ModuleCat.{u} Λ1)).mapDerivedCategory)
          (etaleDerivedPushforward (Over.hom P.obj.right))).hom.app K :=
  sorry

/-- Remark 63.10.8 (2): for a homomorphism `φ : Λ1 →+* Λ2` of torsion rings and a
separated finite-type morphism `f = X.hom` of quasi-compact quasi-separated
schemes, `Rf_!` commutes with derived extension of scalars
`- ⊗_Λ1^L Λ2 : D(-, Λ1) ⥤ D(-, Λ2)`. -/
@[stacks 0GL6]
def etaleDerivedLowerShriekExtendScalarsIso
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2) :
    (etaleDerivedLowerShriek X P ⋙ etaleDerivedExtendScalars φ Y :
        EtaleDerived X.left Λ1 ⥤ EtaleDerived Y Λ2) ≅
      (etaleDerivedExtendScalars φ X.left ⋙ etaleDerivedLowerShriek X P) :=
  Functor.associator
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ1)).mapDerivedCategory)
      (etaleDerivedPushforward (Over.hom P.obj.right))
      (etaleDerivedExtendScalars φ Y) ≪≫
    Functor.isoWhiskerLeft
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ1)).mapDerivedCategory)
      (etaleDerivedExtendScalars_pushforwardIso φ (Over.hom P.obj.right)) ≪≫
    (Functor.associator
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ1)).mapDerivedCategory)
      (etaleDerivedExtendScalars φ (Over.left P.obj.right))
      (etaleDerivedPushforward (Over.hom P.obj.right))).symm ≪≫
    Functor.isoWhiskerRight
      (etaleDerivedExtendScalars_extensionByZeroIso φ
        (Compactification.Of.ι P))
      (etaleDerivedPushforward (Over.hom P.obj.right)) ≪≫
    Functor.associator (etaleDerivedExtendScalars φ X.left)
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ2)).mapDerivedCategory)
      (etaleDerivedPushforward (Over.hom P.obj.right))

/-- Evaluating the derived extension-of-scalars comparison on an object of
`D(X_étale, Λ1)`. -/
theorem etaleDerivedLowerShriekExtendScalarsIso_hom_app
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2)
    (K : EtaleDerived X.left Λ1) :
    (etaleDerivedLowerShriekExtendScalarsIso X φ P hΛ1 hΛ2).hom.app K =
      (Functor.associator
          ((etaleExtensionByZero (Compactification.Of.ι P)
              (ModuleCat.{u} Λ1)).mapDerivedCategory)
          (etaleDerivedPushforward (Over.hom P.obj.right))
          (etaleDerivedExtendScalars φ Y) ≪≫
        Functor.isoWhiskerLeft
          ((etaleExtensionByZero (Compactification.Of.ι P)
              (ModuleCat.{u} Λ1)).mapDerivedCategory)
          (etaleDerivedExtendScalars_pushforwardIso φ (Over.hom P.obj.right)) ≪≫
        (Functor.associator
          ((etaleExtensionByZero (Compactification.Of.ι P)
              (ModuleCat.{u} Λ1)).mapDerivedCategory)
          (etaleDerivedExtendScalars φ (Over.left P.obj.right))
          (etaleDerivedPushforward (Over.hom P.obj.right))).symm ≪≫
        Functor.isoWhiskerRight
          (etaleDerivedExtendScalars_extensionByZeroIso φ
            (Compactification.Of.ι P))
          (etaleDerivedPushforward (Over.hom P.obj.right)) ≪≫
        Functor.associator (etaleDerivedExtendScalars φ X.left)
          ((etaleExtensionByZero (Compactification.Of.ι P)
              (ModuleCat.{u} Λ2)).mapDerivedCategory)
          (etaleDerivedPushforward (Over.hom P.obj.right))).hom.app K :=
  sorry

end Etale
end Scheme
end AlgebraicGeometry

end
