/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Tensor
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Dual

@[expose] public section

open CategoryTheory
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ChernPolynomial

variable {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]

/-- The universal polynomial `2 * r * c₂ - (r - 1) * c₁ ^ 2` for the second
Chern class of an endomorphism bundle. -/
def endomorphism : MvPolynomial ℕ ℤ :=
  2 * MvPolynomial.X 0 * MvPolynomial.X 2 -
    (MvPolynomial.X 0 - 1) * MvPolynomial.X 1 ^ 2

/-- The endomorphism Chern polynomial is weighted-homogeneous of degree two when
variable `i` has weight `i`. -/
theorem endomorphism_isWeightedHomogeneous :
    MvPolynomial.IsWeightedHomogeneous id endomorphism 2 := sorry

/-- Evaluation of the endomorphism polynomial is `2 * r * c₂ - (r - 1) * c₁ ^ 2`. -/
theorem eval_endomorphism (classes : ChernClass.Theory δ p)
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    eval δ p classes E endomorphism =
      2 * variableValue δ p classes E 0 * variableValue δ p classes E 2 -
        (variableValue δ p classes E 0 - 1) * variableValue δ p classes E 1 ^ 2 := sorry

end AlgebraicGeometry.ChernPolynomial

namespace AlgebraicGeometry.ChernClass.Theory

/-- The second Chern class of the tensor product of a finite locally free module
with its dual is the degree-two value of the endomorphism Chern polynomial. -/
theorem component_endomorphism_two
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree] :
    classes.component (E ⊗ Scheme.Modules.dual E) 2 =
      ChernPolynomial.homogeneousValue δ p classes E ChernPolynomial.endomorphism 2
        ChernPolynomial.endomorphism_isWeightedHomogeneous := sorry

end AlgebraicGeometry.ChernClass.Theory
