/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton.Evaluation
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChernPolynomial.Newton

/-- For a short exact sequence of finite locally free modules, the degree-`i`
Newton value of the middle term is the sum of those of the endpoints. -/
theorem value_eq_add_of_shortExact
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : ChernClass.Theory δ p) (C : ShortComplex X.Modules)
    [C.X₁.IsFiniteLocallyFree] [C.X₂.IsFiniteLocallyFree] [C.X₃.IsFiniteLocallyFree]
    (hC : C.ShortExact) (i : ℕ) :
    value δ p classes C.X₂ i =
      value δ p classes C.X₁ i + value δ p classes C.X₃ i := sorry

end AlgebraicGeometry.ChernPolynomial.Newton
