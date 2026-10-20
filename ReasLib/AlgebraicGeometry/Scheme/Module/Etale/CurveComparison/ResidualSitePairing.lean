/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualCharacterPairing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteHigherEquivariance

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.CompactResidual
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k) [hcurve : Curve X] [hsmooth : Smooth X.hom]
variable [hconnected : GeometricallyConnected X.hom]
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [∀ U : (geometricBaseChange X).Etale,
    HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [EnoughInjectives (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)))]
variable [HasDerivedCategory (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [(geometricBaseChange X).smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]

/-- Finite compact coefficients have a finite continuous character module. The
object is the actual continuous dual, with its contragredient arithmetic action. -/
def finiteArithmeticCharacter
    (K : CompactRepresentation.Cat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))))
    [Finite K.obj.V.toModule] :
    (finiteTypeDiscreteModule Λ
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory :=
  ⟨CompactRepresentation.continuousDual Λ
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))) K, by sorry⟩

include hcurve hsmooth hconnected

/-- The compact character comparison followed by the actual higher site
comparison, retaining the two independently defined residual actions. -/
def residualSiteCharacterIso
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    (K : CompactRepresentation.Cat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))))
    [Finite K.obj.V.toModule] (n : ℕ) :
    ((CompactModule.forget Λ).mapAction Gal(AlgebraicClosure k/k)).obj
      (geometricHomologyGaloisAction Λ X ηbar K n) ≅
    characterGaloisAction Λ
      ((AmbientCurve.finiteGeometricCohomologyGaloisFunctor Λ X ηbar n).obj
        (finiteArithmeticCharacter Λ X ηbar K)) :=
  residualCharacterGaloisIso Λ X ηbar K n ≪≫
    characterGaloisIso Λ (AmbientCurve.finiteHigherEquivariantIso Λ X ηbar h_ne_P1 hΛ
      (finiteArithmeticCharacter Λ X ηbar K) n)

/-- Evaluation on actual site cohomology of the published associated sheaf.
This is the compact homology/character pairing; compact-support duality is not
assumed in its construction. -/
def residualSiteEvaluation
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    (K : CompactRepresentation.Cat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))))
    [Finite K.obj.V.toModule] (n : ℕ)
    (x : (geometricHomologyGaloisAction Λ X ηbar K n).V.toModule)
    (c : geometricModuleEtaleHq X
      ((associatedSheafFunctor Λ (arithmeticPoint X ηbar)).obj
        (finiteArithmeticCharacter Λ X ηbar K)) n) : AddCircle (1 : ℚ) :=
  let χ : CharacterModule (geometricModuleEtaleHq X
      ((associatedSheafFunctor Λ (arithmeticPoint X ηbar)).obj
        (finiteArithmeticCharacter Λ X ηbar K)) n) :=
    (residualSiteCharacterIso Λ X ηbar h_ne_P1 hΛ K n).hom.hom x
  χ c

/-- Simultaneous residual translation leaves the specified evaluation unchanged. -/
theorem residualSiteEvaluation_galois
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    (K : CompactRepresentation.Cat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))))
    [Finite K.obj.V.toModule] (n : ℕ) (σ : Gal(AlgebraicClosure k/k))
    (x : (geometricHomologyGaloisAction Λ X ηbar K n).V.toModule)
    (c : geometricModuleEtaleHq X
      ((associatedSheafFunctor Λ (arithmeticPoint X ηbar)).obj
        (finiteArithmeticCharacter Λ X ηbar K)) n) :
    residualSiteEvaluation Λ X ηbar h_ne_P1 hΛ K n
      (CompactModule.linear Λ ((geometricHomologyGaloisAction Λ X ηbar K n).ρ σ) x)
      (((AmbientCurve.finiteGeometricCohomologyGaloisFunctor Λ X ηbar n).obj
        (finiteArithmeticCharacter Λ X ηbar K)).ρ σ |>.hom <| c) =
    residualSiteEvaluation Λ X ηbar h_ne_P1 hΛ K n x c := sorry

end AlgebraicGeometry.SchemeOverField.CompactResidual
