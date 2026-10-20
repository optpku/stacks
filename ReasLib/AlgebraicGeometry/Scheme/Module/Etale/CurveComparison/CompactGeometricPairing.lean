/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AmbientDerivedComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactFiniteInput

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.AmbientCurve
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k) [hcurve : Curve X] [hsmooth : Smooth X.hom]
variable [hconnected : GeometricallyConnected X.hom] [ConnectedSpace (geometricBaseChange X)]
variable (ηbar : GeometricPoint (geometricBaseChange X))
variable [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : (geometricBaseChange X).Etale,
    HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [EnoughInjectives (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)))]
variable [HasDerivedCategory (ModuleCat.{u + 1} Λ)]

/-- Kuhn's actual compact finite input uses the same geometric group and coefficient universe. -/
def compactGeometricInput
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))) [Finite M.obj.V] :=
  CompactRepresentation.finiteCompactification Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) M

/-- The geometric character coefficient is the actual continuous dual of the compact input;
its sheaf is the constructed realization. -/
def geometricCharacterInput
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))) [Finite M.obj.V] :=
  CompactRepresentation.continuousDual Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))
    (compactGeometricInput Λ X ηbar M)

include hcurve hsmooth hconnected

/-- The explicit comparison from Kuhn's ordinary continuous cohomology to geometric
derived sections is the actual resolution and derived-unit comparison. -/
def compactCharacterGeometricCohomologyIso
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))) [Finite M.obj.V] (n : ℕ) :=
  higherComparisonIso Λ X ηbar h_ne_P1 hΛ (geometricCharacterInput Λ X ηbar M) n

/-- Genuine compact homology maps to characters of genuine geometric derived
cohomology through Kuhn's cycle-evaluation comparison and the explicit higher comparison.
This is the untwisted geometric-group boundary, not yet an Hc/trace identification. -/
def compactHomologyGeometricCharacterIso
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))) [Finite M.obj.V] (n : ℕ) :=
  CompactRepresentation.compactHomologyCharacterIso Λ
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) (compactGeometricInput Λ X ηbar M)
      (CompactRepresentation.finiteDualResolution Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) M) n ≪≫
    (CharacterModule.congr
      (compactCharacterGeometricCohomologyIso Λ X ηbar h_ne_P1 hΛ M n).toLinearEquiv).toModuleIso

/-- The connected pairing evaluates the specified character on the specified
geometric cohomology class. No zero map or arbitrary group/scheme iso enters it. -/
def compactGeometricPairing
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))) [Finite M.obj.V] (n : ℕ)
    (x : ((CompactRepresentation.continuousHomology Λ
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) n).obj
        (compactGeometricInput Λ X ηbar M)).toModule)
    (c : geometricDerivedCohomology Λ X ηbar (geometricCharacterInput Λ X ηbar M) n) :
    AddCircle (1 : ℚ) :=
  (compactHomologyGeometricCharacterIso Λ X ηbar h_ne_P1 hΛ M n).hom x c

end AlgebraicGeometry.SchemeOverField.AmbientCurve
