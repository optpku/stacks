module

public import Mathlib.GroupTheory.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport.ChangeOfRings
public import stacks_project.Chap59.Definition_59_77_1
import StacksCheckRecall

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

/- Remark 63.10.8. Restriction of scalars and derived extension of scalars
commute with derived lower shriek for homomorphisms of torsion rings. -/
@[stacks 0GL6] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriekRestrictScalarsIso X φ P :
    (hΛ1 : AddMonoid.IsTorsion Λ1) → (hΛ2 : AddMonoid.IsTorsion Λ2) →
      (etaleDerivedLowerShriek X P ⋙ etaleDerivedRestrictScalars φ Y :
        EtaleDerived X.left Λ2 ⥤ EtaleDerived Y Λ1) ≅
      (etaleDerivedRestrictScalars φ X.left ⋙ etaleDerivedLowerShriek X P))

#check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriekExtendScalars_isIso X φ P :
    (hΛ1 : AddMonoid.IsTorsion Λ1) → (hΛ2 : AddMonoid.IsTorsion Λ2) →
      IsIso (etaleDerivedLowerShriekExtendScalars_comparison X φ P hΛ1 hΛ2))
end Etale
end Scheme
end AlgebraicGeometry

end
