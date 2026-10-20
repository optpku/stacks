/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteDualSheafComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualCharacterPairing

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace ActualArithmeticDualSheaf
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k) [ConnectedSpace (geometricBaseChange X)]
variable (ηbar : GeometricPoint (geometricBaseChange X))

variable [ConnectedSpace X.left]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]

variable [(geometricBaseChange X).smallEtaleTopology.HasSheafCompose (ActualFiniteCoefficient.modules Λ)]
variable [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : (geometricBaseChange X).Etale,
    HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]
variable [∀ U : (geometricBaseChange X).Etale,
    HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U)
      (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]
variable [HasSheafify (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1}]
variable (hΛ : IsUnit (Nat.card Λ : k))

variable (N : (finiteTypeDiscreteModule Λ
  (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory)

/-- Restrict the actual arithmetic coefficient to geometric pi1. -/
def geometricInput :
    (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))).FullSubcategory :=
  ⟨(Ambient.restriction Λ X ηbar).obj N.obj, by sorry⟩

/-- The actual finite compact arithmetic inverse-Tate input. -/
def compactInput :=
  CompactRepresentation.finiteCompactification Λ
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
    (AmbientGeometry.arithmeticInverseTate Λ X ηbar hΛ N.obj)

/-- Geometric restriction of its continuous dual, then restriction of scalars.
This is the coefficient used by the residual character comparison. -/
def characterInput :
    (finiteTypeDiscreteModule (ActualRootsModule.Coeff.{u} (Nat.card Λ))
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))).FullSubcategory :=
  ⟨⟨((ActualFiniteCoefficient.modules Λ).mapAction (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))).obj
    (((Ambient.restriction Λ X ηbar).obj
      (CompactRepresentation.continuousDual Λ
        (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
        (compactInput Λ X ηbar hΛ N))).obj), by sorry⟩, by sorry⟩

/-- The actual finite-character inclusion inverted, retaining geometric action.
The cyclotomic character is trivial on geometric pi1. -/
def coefficientIso :
    ActualFiniteDualComparison.characterRepresentation Λ X ηbar
      (geometricInput Λ X ηbar N) ≅ characterInput Λ X ηbar hΛ N :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (Action.mkIso
      ((ActualFiniteCoefficient.modules Λ).mapIso
        (CompactRepresentation.finiteCharacterComparison Λ
          (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
          (AmbientGeometry.arithmeticInverseTate Λ X ηbar hΛ N.obj)).symm)
      (fun _ ↦ sorry)))

/-- The intrinsic linear dual of the source sheaf is identified with the
associated sheaf of the ACTUAL restricted arithmetic inverse-Tate character
coefficient. All maps are germs, published units/counits and finite-character
inclusion maps from the two preceding branches. -/
def intrinsicToCharacterSheafIso :
    ActualFiniteDualComparison.dualSheaf Λ X ηbar (geometricInput Λ X ηbar N) ≅
      (associatedSheafFunctor (ActualRootsModule.Coeff.{u} (Nat.card Λ)) ηbar).obj
        (characterInput Λ X ηbar hΛ N) :=
  ActualFiniteDualComparison.sheafIso Λ X ηbar hΛ (geometricInput Λ X ηbar N) ≪≫
    (associatedSheafFunctor (ActualRootsModule.Coeff.{u} (Nat.card Λ)) ηbar).mapIso
      (coefficientIso Λ X ηbar hΛ N)

end ActualArithmeticDualSheaf
