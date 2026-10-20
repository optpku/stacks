module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Presentation
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Points

/-!
# Restriction of a groupoid scheme

This compatibility module re-exports the restriction construction, its fibre-product
presentation, and its description on points.
-/

open CategoryTheory

universe u

#check
  (AlgebraicGeometry.GroupoidScheme.pullback :
    {S : AlgebraicGeometry.Scheme.{u}} →
      (G : AlgebraicGeometry.GroupoidScheme S) →
      {U' : Over S} → (g : U' ⟶ G.U) →
        AlgebraicGeometry.GroupoidScheme S)
