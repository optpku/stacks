module

public import ReasLib.AlgebraicGeometry.ChowGroup.Rational
public import ReasLib.AlgebraicGeometry.ChowGroup.TotalFundamental
public import ReasLib.AlgebraicGeometry.LocalizedChern.TotalCap
public import ReasLib.AlgebraicGeometry.Scheme.K0.Chow

/-!
# Localized Chern character capped on the fundamental class

The rational total Chow group and the coherent Chern-cap comparison are provided by
their mathematical owners.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Proposition 42.57.1: Rational total Chow homology is the tensor product of the
total relative Chow group with the rational numbers. -/
#check (AlgebraicGeometry.ChowGroup.rationalChow :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom], Type u)
