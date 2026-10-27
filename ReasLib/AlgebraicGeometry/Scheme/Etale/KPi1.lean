/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualDerivedComparison
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-! # Canonical étale K(π, 1) comparison -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField
variable {k : Type u} [Field k] (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))

/-- The canonical residual derived comparison is invertible for finite coefficients
of cardinality invertible in the ground field, on the all-discrete module categories. -/
class IsEtaleKPi1 : Prop where
  /-- Invertibility of the specified derived-composition comparison. -/
  comparison_isIso : ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
      [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
        (smallEtalePullback f).op.HasLeftKanExtension F]
      [∀ U : X.left.Etale,
        HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
      [∀ U : (geometricBaseChange X).Etale,
        HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
      [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R))]
      [HasDerivedCategory.{u + 2} (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R))]
      [HasDerivedCategory.{u + 2} (DiscreteModuleCat R (NoncommResidualSectionsComparison.Γ X η))]
      [HasDerivedCategory.{u + 2} (DiscreteModuleCat R (NoncommResidualSectionsComparison.Q X η))],
      IsUnit (Nat.card R : k) → IsIso (NoncommResidualDerivedComparison.comparison R X η)

/-- The étale K(π, 1) property is invertibility of the canonical residual comparison. -/
theorem IsEtaleKPi1.spec : IsEtaleKPi1 X η ↔
    ∀ (R : Type (u + 1)) [Ring R] [Finite R]
      [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
      [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
        (smallEtalePullback f).op.HasLeftKanExtension F]
      [∀ U : X.left.Etale,
        HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
      [∀ U : (geometricBaseChange X).Etale,
        HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
      [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R))]
      [HasDerivedCategory.{u + 2} (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R))]
      [HasDerivedCategory.{u + 2} (DiscreteModuleCat R (NoncommResidualSectionsComparison.Γ X η))]
      [HasDerivedCategory.{u + 2} (DiscreteModuleCat R (NoncommResidualSectionsComparison.Q X η))],
      IsUnit (Nat.card R : k) → IsIso (NoncommResidualDerivedComparison.comparison R X η) := sorry

/-- Smooth geometrically irreducible curves other than geometric P¹ are étale K(π, 1). -/
instance isEtaleKPi1_curve [Curve X] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1)] :
    IsEtaleKPi1 X η where
  comparison_isIso := sorry

end AlgebraicGeometry.SchemeOverField
