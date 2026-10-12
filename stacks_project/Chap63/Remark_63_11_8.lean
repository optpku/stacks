/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import stacks_project.Chap63.«63_11_4_1_UpperShriek»
public import stacks_project.Chap63.Remark_63_10_8
import Mathlib.Tactic.CrossRefAttribute

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

/-- Remark 63.11.8: for a homomorphism `φ : Λ1 →+* Λ2` of torsion rings and a
separated finite-type morphism `f = X.hom` of quasi-compact quasi-separated
schemes, derived restriction of scalars commutes with `Rf^!`:
`etaleDerivedUpperShriek X Λ2 P ⋙ etaleDerivedRestrictScalars φ X.left ≅
etaleDerivedRestrictScalars φ Y ⋙ etaleDerivedUpperShriek X Λ1 P` on
`D(Y_étale, Λ2)` and `D(X_étale, Λ1)`. This is the uniqueness-of-adjoints
conjugate of `etaleDerivedLowerShriekExtendScalarsIso` along the composite
adjunctions `etaleDerivedExtendRestrictAdjunction` then
`etaleDerivedLowerShriekAdjunction`. -/
@[stacks 0GLF]
def etaleDerivedUpperShriekRestrictScalarsIso
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2) :
    (etaleDerivedUpperShriek X Λ2 P ⋙ etaleDerivedRestrictScalars φ X.left :
        EtaleDerived Y Λ2 ⥤ EtaleDerived X.left Λ1) ≅
      (etaleDerivedRestrictScalars φ Y ⋙ etaleDerivedUpperShriek X Λ1 P) :=
  conjugateIsoEquiv
    ((etaleDerivedExtendRestrictAdjunction φ X.left).comp
      (etaleDerivedLowerShriekAdjunction X Λ2 P))
    ((etaleDerivedLowerShriekAdjunction X Λ1 P).comp
      (etaleDerivedExtendRestrictAdjunction φ Y))
    (etaleDerivedLowerShriekExtendScalarsIso X φ P hΛ1 hΛ2)

/-- Evaluating the derived restriction-of-scalars comparison for `Rf^!` on an
object of `D(Y_étale, Λ2)`. -/
def etaleDerivedUpperShriekRestrictScalarsIso_app
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2)
    (K : EtaleDerived Y Λ2) :
    (etaleDerivedRestrictScalars φ X.left).obj
      ((etaleDerivedUpperShriek X Λ2 P).obj K) ≅
      (etaleDerivedUpperShriek X Λ1 P).obj
        ((etaleDerivedRestrictScalars φ Y).obj K) :=
  (etaleDerivedUpperShriekRestrictScalarsIso X φ P hΛ1 hΛ2).app K

/-- The `Rf^!` restriction-of-scalars comparison is the conjugate of
`etaleDerivedLowerShriekExtendScalarsIso` along the composite adjunctions
`etaleDerivedExtendRestrictAdjunction` then
`etaleDerivedLowerShriekAdjunction`. -/
theorem etaleDerivedUpperShriekRestrictScalarsIso_spec
    (hΛ1 : AddMonoid.IsTorsion Λ1) (hΛ2 : AddMonoid.IsTorsion Λ2) :
    etaleDerivedUpperShriekRestrictScalarsIso X φ P hΛ1 hΛ2 =
      conjugateIsoEquiv
        ((etaleDerivedExtendRestrictAdjunction φ X.left).comp
          (etaleDerivedLowerShriekAdjunction X Λ2 P))
        ((etaleDerivedLowerShriekAdjunction X Λ1 P).comp
          (etaleDerivedExtendRestrictAdjunction φ Y))
        (etaleDerivedLowerShriekExtendScalarsIso X φ P hΛ1 hΛ2) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
