/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.GroupTheory.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport

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

/-- Derived lower shriek commutes with restriction of scalars along a
homomorphism of torsion coefficient rings. -/
def etaleDerivedLowerShriekRestrictScalarsIso
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2) :
    (etaleDerivedLowerShriek X P ⋙ etaleDerivedRestrictScalars φ Y :
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ2)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1))) ≅
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
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ2))) :
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
  rfl

/-- The compactification comparison from derived lower shriek followed by
extension of scalars to extension of scalars followed by derived lower shriek. -/
def etaleDerivedLowerShriekExtendScalars_comparison
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2) :
    (etaleDerivedLowerShriek X P ⋙ etaleDerivedExtendScalars φ Y :
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ1)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2))) ⟶
      (etaleDerivedExtendScalars φ X.left ⋙ etaleDerivedLowerShriek X P) :=
  (Functor.associator
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ1)).mapDerivedCategory)
      (etaleDerivedPushforward (Over.hom P.obj.right))
      (etaleDerivedExtendScalars φ Y)).hom ≫
    Functor.whiskerLeft
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ1)).mapDerivedCategory)
      (etaleDerivedExtendScalars_pushforwardComparison φ (Over.hom P.obj.right) hΛ1 hΛ2) ≫
    (Functor.associator
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ1)).mapDerivedCategory)
      (etaleDerivedExtendScalars φ (Over.left P.obj.right))
      (etaleDerivedPushforward (Over.hom P.obj.right))).inv ≫
    Functor.whiskerRight
      (etaleDerivedExtendScalars_extensionByZeroComparison φ
        (Compactification.Of.ι P))
      (etaleDerivedPushforward (Over.hom P.obj.right)) ≫
    (Functor.associator (etaleDerivedExtendScalars φ X.left)
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ2)).mapDerivedCategory)
      (etaleDerivedPushforward (Over.hom P.obj.right))).hom

/-- Derived lower shriek commutes with derived extension of scalars along a
homomorphism of torsion rings. -/
instance etaleDerivedLowerShriekExtendScalars_isIso
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2) :
    IsIso (etaleDerivedLowerShriekExtendScalars_comparison X φ P hΛ1 hΛ2) :=
  sorry

/-- The component of the lower-shriek extension-of-scalars comparison is the
pasted extension-by-zero and proper-pushforward comparison. -/
theorem etaleDerivedLowerShriekExtendScalars_comparison_app
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2)
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ1))) :
    (etaleDerivedLowerShriekExtendScalars_comparison X φ P hΛ1 hΛ2).app K =
      ((Functor.associator
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ1)).mapDerivedCategory)
      (etaleDerivedPushforward (Over.hom P.obj.right))
      (etaleDerivedExtendScalars φ Y)).hom ≫
    Functor.whiskerLeft
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ1)).mapDerivedCategory)
      (etaleDerivedExtendScalars_pushforwardComparison φ (Over.hom P.obj.right) hΛ1 hΛ2) ≫
    (Functor.associator
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ1)).mapDerivedCategory)
      (etaleDerivedExtendScalars φ (Over.left P.obj.right))
      (etaleDerivedPushforward (Over.hom P.obj.right))).inv ≫
    Functor.whiskerRight
      (etaleDerivedExtendScalars_extensionByZeroComparison φ
        (Compactification.Of.ι P))
      (etaleDerivedPushforward (Over.hom P.obj.right)) ≫
    (Functor.associator (etaleDerivedExtendScalars φ X.left)
      ((etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ2)).mapDerivedCategory)
      (etaleDerivedPushforward (Over.hom P.obj.right))).hom).app K :=
  rfl

variable [(etaleDerivedLowerShriek X P : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ1)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1))).IsLeftAdjoint]
variable [(etaleDerivedLowerShriek X P : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ2)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2))).IsLeftAdjoint]

/-- The restriction-of-scalars upper-shriek comparison is the right-adjoint
conjugate of the extension-of-scalars lower-shriek comparison. -/
def etaleDerivedUpperShriekRestrictScalars_comparison
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2) :
    ((etaleDerivedLowerShriek X P : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ2)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2))).rightAdjoint ⋙ etaleDerivedRestrictScalars φ X.left :
        DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2)) ⥤ DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ1))) ⟶
      (etaleDerivedRestrictScalars φ Y ⋙ (etaleDerivedLowerShriek X P : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ1)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1))).rightAdjoint) :=
  conjugateEquiv
    ((etaleDerivedExtendRestrictAdjunction φ X.left).comp
      (Adjunction.ofIsLeftAdjoint (etaleDerivedLowerShriek X P : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ2)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2)))))
    ((Adjunction.ofIsLeftAdjoint (etaleDerivedLowerShriek X P : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ1)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1)))).comp
      (etaleDerivedExtendRestrictAdjunction φ Y))
    (etaleDerivedLowerShriekExtendScalars_comparison X φ P hΛ1 hΛ2)

/-- The restriction-of-scalars comparison for the right adjoint of derived
lower shriek is invertible over torsion coefficient rings. -/
instance etaleDerivedUpperShriekRestrictScalars_isIso
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2) :
    IsIso (etaleDerivedUpperShriekRestrictScalars_comparison X φ P hΛ1 hΛ2) :=
  sorry

/-- Each component of the restriction-of-scalars upper-shriek comparison is
invertible over torsion coefficient rings. -/
instance etaleDerivedUpperShriekRestrictScalars_comparison_app_isIso
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2))) :
    IsIso ((etaleDerivedUpperShriekRestrictScalars_comparison X φ P hΛ1 hΛ2).app K) :=
  sorry

/-- The upper-shriek restriction comparison is obtained by conjugation along
the composite extension-restriction and lower-shriek adjunctions. -/
theorem etaleDerivedUpperShriekRestrictScalars_comparison_spec
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2) :
    etaleDerivedUpperShriekRestrictScalars_comparison X φ P hΛ1 hΛ2 =
      conjugateEquiv
    ((etaleDerivedExtendRestrictAdjunction φ X.left).comp
      (Adjunction.ofIsLeftAdjoint (etaleDerivedLowerShriek X P : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ2)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ2)))))
    ((Adjunction.ofIsLeftAdjoint (etaleDerivedLowerShriek X P : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ1)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ1)))).comp
      (etaleDerivedExtendRestrictAdjunction φ Y))
    (etaleDerivedLowerShriekExtendScalars_comparison X φ P hΛ1 hΛ2) :=
  rfl

end Etale
end Scheme
end AlgebraicGeometry

end
