/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommArithmeticTate
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompletedTransport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualCompletedTarget

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace NoncommSourceTarget
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))
variable (hR : IsUnit (Nat.card R : k))
variable (M : (finiteTypeDiscreteModule R
  (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))).FullSubcategory)

/-- The actual residual fiber group in the common fundamental-group universe. -/
abbrev residualGroup := ActualResidualCompletedTarget.residualGroup X η

/-- The corrected noncommutative compact inverse-Tate tensor cochain over the
independently defined residual quotient group. -/
def residualCochain := NoncommDerivedTensor.tensorCochain Rᵐᵒᵖ
  (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber η))
  (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η))) (residualGroup X η)
  (geometricToArithmetic X η).hom (arithmeticToGalois X (arithmeticPoint X η)).hom
  (geometricToArithmetic_range_eq_arithmeticToGalois_ker X η)
  (arithmeticToGalois_surjective X (arithmeticPoint X η))
  (NoncommArithmeticTate.compactInput R X η hR M)

/-- Canonical scalar normalization removes the double opposite on every coefficient. -/
def coefficientNormalizedCochain :=
  ((NoncommCompletedTransport.doubleOppositeModules R (G := residualGroup X η)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (residualCochain R X η hR M)

/-- Residual-group naming transport uses the actual continuous finite-fiber
Galois comparison in both directions. -/
def toGaloisModules := completedGroupRing.restrictScalars R
  (ActualResidualCompletedTarget.residualEquiv X η)
  (ActualResidualCompletedTarget.residualEquiv_continuous X η)
  (ActualResidualCompletedTarget.residualEquiv_inverse_continuous X η)

instance toGaloisModules_additive : (toGaloisModules R X η).Additive :=
  inferInstanceAs ((completedGroupRing.restrictScalars R
    (ActualResidualCompletedTarget.residualEquiv X η)
    (ActualResidualCompletedTarget.residualEquiv_continuous X η)
    (ActualResidualCompletedTarget.residualEquiv_inverse_continuous X η)).Additive)

/-- Full noncommutative group-side target over the original general field. -/
def galoisCochain := ((toGaloisModules R X η).mapHomologicalComplex (ComplexShape.up ℤ)).obj
  (coefficientNormalizedCochain R X η hR M)

variable [HasDerivedCategory (ModuleCat.{u + 1}
  (completedGroupRing R Gal(AlgebraicClosure k/k)))]

/-- The target object of the approved general-field 03VM signature. The
geometric source and the map to this object must still be assembled explicitly. -/
def derivedTarget := DerivedCategory.Q.obj (galoisCochain R X η hR M)

end NoncommSourceTarget
