module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton.Evaluation

open AlgebraicGeometry CategoryTheory

universe u

/- The chapter compatibility module exposes the canonical Newton evaluation owner. -/
#check (AlgebraicGeometry.ChernPolynomial.Newton.value :
  ∀ {S X : Scheme.{u}} (δ : S → ℤ) (f : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType f]
    (classes : ChernClass.Theory δ f) (E : X.Modules) [E.IsFiniteLocallyFree] (n : ℕ),
    ChowCohomology.Nonnegative.degree δ f n)
