module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AmbientDerivedComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.SiteExtComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ExactDerivedUnit

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.AmbientCurve
open AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
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
variable [HasSheafify (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [(geometricBaseChange X).smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]

/-- Exact realization, its actual derived unit, and the explicit resolution/Ext
comparison identify the geometric bounded-derived model with the existing site cohomology. -/
def geometricDerivedToSiteIso
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))) (n : ℕ) :
    geometricDerivedCohomology Λ X ηbar M n ≅ (realizedCohomology Λ ηbar n).obj M :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) (n : ℤ)).mapIso
      ((Functor.RightDerived.Bounded.functor (sections (X := geometricBaseChange X) Λ)).mapIso
        (ActualResolutionComparison.exactUnitIso (functor (Λ := Λ) (xbar := ηbar)) M).symm) ≪≫
    (ActualResolutionComparison.ordinaryToBoundedIso (sections (X := geometricBaseChange X) Λ)
      (injectiveResolution (obj M)) n).symm ≪≫
    ActualSiteExt.moduleToSiteIso (geometricBaseChange X) Λ (obj M) n

include hcurve hsmooth hconnected

/-- The actual higher comparison now lands in the current site-Ext cohomology API. -/
def higherSiteComparisonIso
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))) (n : ℕ) :
    (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) n).obj M ≅
      (realizedCohomology Λ ηbar n).obj M :=
  higherComparisonIso Λ X ηbar h_ne_P1 hΛ M n ≪≫ geometricDerivedToSiteIso Λ X ηbar M n

/-- Naturality of the explicitly normalized higher site-cohomology comparison. -/
theorem higherSiteComparisonIso_naturality
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    {M N : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))} (a : M ⟶ N) (n : ℕ) :
    (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) n).map a ≫
        (higherSiteComparisonIso Λ X ηbar h_ne_P1 hΛ N n).hom =
      (higherSiteComparisonIso Λ X ηbar h_ne_P1 hΛ M n).hom ≫
        (realizedCohomology Λ ηbar n).map a := sorry

/-- The specified natural comparison uses all-discrete resolutions and the actual
associated-sheaf site cohomology, with no caller-supplied comparison package. -/
def higherSiteComparisonNatIso
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k)) (n : ℕ) :
    CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) n ≅
      realizedCohomology Λ ηbar n :=
  NatIso.ofComponents (fun M ↦ higherSiteComparisonIso Λ X ηbar h_ne_P1 hΛ M n)
    (fun a ↦ higherSiteComparisonIso_naturality Λ X ηbar h_ne_P1 hΛ a n)

/-- Degree zero recovers the original actual sections/germ comparison and derived unit. -/
theorem higherSiteComparison_zero
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k)) :
    higherSiteComparisonNatIso Λ X ηbar h_ne_P1 hΛ 0 = derivedZeroComparison Λ ηbar := sorry

end AlgebraicGeometry.SchemeOverField.AmbientCurve
