module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Geometric

universe u

open AlgebraicGeometry CategoryTheory

/- The geometric Frobenius API is provided by the shared scheme-over-field owner. -/
#check (AlgebraicGeometry.SchemeOverField.geometricFrobeniusOver :
  ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (f : ℕ)
    [Fintype k] (hcard : Fintype.card k = p ^ f)
    (X : AlgebraicGeometry.SchemeOverField k), X ⟶ X)
