/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CurveRealizationAcyclicity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricSections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.DerivedResolutionComparison

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
variable {Y : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable [ConnectedSpace Y] (ybar : GeometricPoint Y)
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [EnoughInjectives (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ybar)))]
variable [HasDerivedCategory (ModuleCat.{u + 1} Λ)]

/-- Module-valued sections are additive through evaluation of the additive sheaf functor. -/
instance sections_additive : (sections (X := Y) Λ).Additive := sorry

/-- Sections preserve finite limits; they are evaluation at the terminal site object. -/
instance sections_preservesFiniteLimits : PreservesFiniteLimits (sections (X := Y) Λ) := sorry

/-- The higher comparison is the canonical bounded-below derived composition map,
with underived normalization supplied by the actual section-germ isomorphism. -/
def derivedComparison :
    Functor.RightDerived.Bounded.functor
        (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.fixedPointsFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ybar))) ⟶
      Functor.RightDerived.Bounded.functor (functor (Λ := Λ) (xbar := ybar)) ⋙
        Functor.RightDerived.Bounded.functor (sections (X := Y) Λ) :=
  Functor.RightDerived.Composition.BoundedBelow.comparisonOfIso
    (functor (Λ := Λ) (xbar := ybar)) (sections Λ) (sectionsIso Λ ybar).symm

end AlgebraicGeometry.Scheme.AmbientAssociatedSheaf

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

include hcurve hsmooth hconnected

/-- The concrete derived comparison is invertible on the source's non-P1 curve:
exact realization sends ambient injectives to sections-acyclic sheaves. -/
theorem derivedComparison_isIso
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k)) : IsIso (derivedComparison Λ ηbar) := sorry

/-- Derived continuous invariants and geometric derived sections are identified
by inverting only the specified composition comparison, under the exact curve hypotheses. -/
def derivedComparisonIso
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k)) :=
  @asIso _ _ _ _ (derivedComparison Λ ηbar) (derivedComparison_isIso Λ X ηbar h_ne_P1 hΛ)

/-- The geometric derived-cohomology model uses exact realization followed by
actual derived global sections of its degree-zero coefficient object. -/
def geometricDerivedCohomology
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))) (n : ℕ) :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) (n : ℤ)).obj
    ((Functor.RightDerived.Bounded.functor (sections (X := geometricBaseChange X) Λ)).obj
      ((Functor.RightDerived.Bounded.functor (functor (Λ := Λ) (xbar := ηbar))).obj
        (ActualResolutionComparison.singleModel M)))

/-- Actual geometric derived cohomology on coefficient morphisms. -/
def geometricDerivedCohomologyFunctor (n : ℕ) :
    DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) ⥤ ModuleCat.{u + 1} Λ :=
  ActualResolutionComparison.singleModelFunctor ⋙
    Functor.RightDerived.Bounded.functor (functor (Λ := Λ) (xbar := ηbar)) ⋙
      Functor.RightDerived.Bounded.functor (sections (X := geometricBaseChange X) Λ) ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) (n : ℤ)

/-- The positive-degree comparison composes the specified injective-resolution
map with homology of the canonical geometric derived comparison. -/
def higherComparisonIso
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))) (n : ℕ) :
    (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) n).obj M ≅
      geometricDerivedCohomology Λ X ηbar M n :=
  ActualResolutionComparison.ordinaryToBoundedIso
      (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.fixedPointsFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)))
      (injectiveResolution M) n ≪≫
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) (n : ℤ)).mapIso
      ((derivedComparisonIso Λ X ηbar h_ne_P1 hΛ).app (ActualResolutionComparison.singleModel M))

/-- The specified resolution and derived-unit comparison is natural in coefficients. -/
theorem higherComparisonIso_naturality
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k))
    {M N : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))} (a : M ⟶ N) (n : ℕ) :
    (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) n).map a ≫
        (higherComparisonIso Λ X ηbar h_ne_P1 hΛ N n).hom =
      (higherComparisonIso Λ X ηbar h_ne_P1 hΛ M n).hom ≫
        (geometricDerivedCohomologyFunctor Λ X ηbar n).map a := sorry

/-- The actual higher comparison as a natural isomorphism of functors on ALL
discrete geometric representations; finite coefficients are included only afterward. -/
def higherComparisonNatIso
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (hΛ : IsUnit (Nat.card Λ : k)) (n : ℕ) :
    CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) n ≅
      geometricDerivedCohomologyFunctor Λ X ηbar n :=
  NatIso.ofComponents (fun M ↦ higherComparisonIso Λ X ηbar h_ne_P1 hΛ M n)
    (fun a ↦ higherComparisonIso_naturality Λ X ηbar h_ne_P1 hΛ a n)

end AlgebraicGeometry.SchemeOverField.AmbientCurve
