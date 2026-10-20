module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Restriction

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Equality of algebraic-space morphisms induces an isomorphism of derived pullback functors. -/
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pullbackCongr :
  ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S} {f g : Y ⟶ X},
    f = g → (ModuleDerived.pullback f ≅ ModuleDerived.pullback g))
