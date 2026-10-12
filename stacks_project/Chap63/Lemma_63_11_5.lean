/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.GroupTheory.Torsion
public import stacks_project.Chap63.«63_11_4_1_Trace»
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

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
variable [MonoidalCategory (EtaleDerived X.left Λ)]
variable [MonoidalClosed (EtaleDerived X.left Λ)]
variable [MonoidalCategory (EtaleDerived (Over.left P.obj.right) Λ)]
variable [MonoidalClosed (EtaleDerived (Over.left P.obj.right) Λ)]
variable [MonoidalCategory (EtaleDerived Y Λ)]
variable [MonoidalClosed (EtaleDerived Y Λ)]
variable [(etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).OplaxMonoidal]
variable [(etaleDerivedExtensionByZeroAdjunction
    (Compactification.Of.ι P) Λ).ProjectionFormulaMap]
variable [(etaleDerivedPushforward (Over.hom P.obj.right) :
    EtaleDerived (Over.left P.obj.right) Λ ⥤ EtaleDerived Y Λ).LaxMonoidal]
variable [((etaleDerivedLowerShriek X P :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)).IsLeftAdjoint]

/-- Lemma 63.11.5: for a separated finite-type morphism `X.hom : X.left ⟶ Y`
of quasi-compact quasi-separated schemes and a torsion ring `Λ`, the
sheafy-trace morphism `etaleDerivedSheafyTrace` of (63.11.4.1),
`Rf_* RHom_Λ(L, Rf^! K) ⟶ RHom_Λ(Rf_! L, K)`, is an isomorphism in
`D(Y_étale, Λ)` for every `K` in `D(Y_étale, Λ)` and
`L` in `D(X_étale, Λ)`. -/
@[stacks 0GLC]
theorem etaleDerivedSheafyTrace_isIso
    (hΛ : AddMonoid.IsTorsion Λ) (L : EtaleDerived X.left Λ)
    (K : EtaleDerived Y Λ) :
    IsIso (etaleDerivedSheafyTrace X P L K) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
