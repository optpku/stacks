module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import stacks_project.Chap63.«63_11_4_1_UpperShriek»
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport.ChangeOfRings
import StacksCheckRecall

/-!
# Change of rings for derived étale upper shriek

Restriction of scalars along a homomorphism of torsion rings commutes with
`Rf^!` by uniqueness of adjoints, as the conjugate of the second diagram of
Remark 63.10.8.
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

namespace AlgebraicGeometry.Scheme.Etale

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
variable [((etaleDerivedLowerShriek X P :
    EtaleDerived X.left Λ1 ⥤ EtaleDerived Y Λ1)).IsLeftAdjoint]
variable [((etaleDerivedLowerShriek X P :
    EtaleDerived X.left Λ2 ⥤ EtaleDerived Y Λ2)).IsLeftAdjoint]

/- Remark 63.11.8. Restriction of scalars commutes with derived upper shriek
as the right-adjoint conjugate of the lower-shriek extension comparison. -/
@[stacks 0GLF] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedUpperShriekRestrictScalars_isIso X φ P :
    (hΛ1 : AddMonoid.IsTorsion Λ1) → (hΛ2 : AddMonoid.IsTorsion Λ2) →
      IsIso (etaleDerivedUpperShriekRestrictScalars_comparison X φ P hΛ1 hΛ2))

#check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedUpperShriekRestrictScalars_comparison X φ P :
    (hΛ1 : AddMonoid.IsTorsion Λ1) → (hΛ2 : AddMonoid.IsTorsion Λ2) →
      (etaleDerivedUpperShriek X Λ2 P ⋙ etaleDerivedRestrictScalars φ X.left :
        EtaleDerived Y Λ2 ⥤ EtaleDerived X.left Λ1) ⟶
      (etaleDerivedRestrictScalars φ Y ⋙ etaleDerivedUpperShriek X Λ1 P))

#check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedUpperShriekRestrictScalars_comparison_app_isIso X φ P :
    (hΛ1 : AddMonoid.IsTorsion Λ1) → (hΛ2 : AddMonoid.IsTorsion Λ2) →
    (K : EtaleDerived Y Λ2) →
      IsIso ((etaleDerivedUpperShriekRestrictScalars_comparison X φ P hΛ1 hΛ2).app K))

#check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedUpperShriekRestrictScalars_comparison_spec X φ P :
    (hΛ1 : AddMonoid.IsTorsion Λ1) → (hΛ2 : AddMonoid.IsTorsion Λ2) →
      etaleDerivedUpperShriekRestrictScalars_comparison X φ P hΛ1 hΛ2 =
        conjugateEquiv
          ((etaleDerivedExtendRestrictAdjunction φ X.left).comp
            (etaleDerivedLowerShriekAdjunction X Λ2 P))
          ((etaleDerivedLowerShriekAdjunction X Λ1 P).comp
            (etaleDerivedExtendRestrictAdjunction φ Y))
          (etaleDerivedLowerShriekExtendScalars_comparison X φ P hΛ1 hΛ2))

end AlgebraicGeometry.Scheme.Etale

end
