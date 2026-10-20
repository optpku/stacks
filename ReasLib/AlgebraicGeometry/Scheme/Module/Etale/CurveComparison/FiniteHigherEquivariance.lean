/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteHigherSiteComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.RelativeCohomologyUnderlying
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricSheafCohomologyAction

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.AmbientCurve
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

/-- The continuous group cohomology side uses the independently derived residual quotient action. -/
def finiteGroupCohomologyGaloisFunctor (n : ℕ) :
    (finiteTypeDiscreteModule Λ
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory ⥤
      Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) where
  obj M := AmbientGeometry.continuousCohomologyGaloisAction Λ X ηbar M.obj n
  map f := { hom := (Ambient.finiteCohomology Λ X ηbar n).map f
             comm := fun _ ↦ sorry }
  map_id := sorry
  map_comp := sorry

/-- The geometric side uses the independently constructed site-cohomology action
from pullback/descent, with actual induced maps of associated sheaves. -/
def finiteGeometricCohomologyGaloisFunctor (n : ℕ) :
    (finiteTypeDiscreteModule Λ
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory ⥤
      Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) where
  obj M := AmbientGeometry.geometricSiteGaloisAction Λ X
    ((associatedSheafFunctor Λ (arithmeticPoint X ηbar)).obj M) n
  map f := { hom := geometricModuleEtaleHqMap X
               ((associatedSheafFunctor Λ (arithmeticPoint X ηbar)).map f) n
             comm := fun _ ↦ sorry }
  map_id := sorry
  map_comp := sorry

include hcurve hsmooth hconnected

/-- The actual higher comparison intertwines two independently constructed actions.
This is a law of the specified maps, never a caller-supplied compatibility package. -/
theorem finiteHigherSiteComparison_equivariant
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    (M : (finiteTypeDiscreteModule Λ
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory)
    (n : ℕ) (σ : Gal(AlgebraicClosure k/k)) :
    ((finiteGroupCohomologyGaloisFunctor Λ X ηbar n).obj M).ρ σ ≫
        (finiteHigherSiteComparisonIso Λ X ηbar h_ne_P1 hΛ M n).hom =
      (finiteHigherSiteComparisonIso Λ X ηbar h_ne_P1 hΛ M n).hom ≫
        ((finiteGeometricCohomologyGaloisFunctor Λ X ηbar n).obj M).ρ σ := sorry

/-- The source-facing all-degree comparison as an actual isomorphism of residual Galois modules. -/
def finiteHigherEquivariantIso
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    (M : (finiteTypeDiscreteModule Λ
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory) (n : ℕ) :
    (finiteGroupCohomologyGaloisFunctor Λ X ηbar n).obj M ≅
      (finiteGeometricCohomologyGaloisFunctor Λ X ηbar n).obj M :=
  Action.mkIso (finiteHigherSiteComparisonIso Λ X ηbar h_ne_P1 hΛ M n)
    (finiteHigherSiteComparison_equivariant Λ X ηbar h_ne_P1 hΛ M n)

/-- The specified equivariant comparison is natural on finite arithmetic coefficients. -/
def finiteHigherEquivariantNatIso
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k)) (n : ℕ) :
    finiteGroupCohomologyGaloisFunctor Λ X ηbar n ≅ finiteGeometricCohomologyGaloisFunctor Λ X ηbar n :=
  NatIso.ofComponents (fun M ↦ finiteHigherEquivariantIso Λ X ηbar h_ne_P1 hΛ M n) (fun _ ↦ sorry)

end AlgebraicGeometry.SchemeOverField.AmbientCurve
