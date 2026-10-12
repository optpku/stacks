/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton.Evaluation
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Tensor

@[expose] public section

open CategoryTheory
open scoped BigOperators MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ChernPolynomial.Newton

/-- The degree-`n` Newton value of a tensor product is the binomial convolution of
the Newton values of its factors in degree `n`. -/
theorem value_tensor {S X : Scheme.{u}} (δ : S → ℤ) (f : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType f]
    (classes : ChernClass.Theory δ f) (E₁ E₂ : X.Modules)
    [E₁.IsFiniteLocallyFree] [E₂.IsFiniteLocallyFree] (n : ℕ) :
    ChernClass.homogeneous δ f n (value δ f classes (E₁ ⊗ E₂) n) =
      ∑ j ∈ Finset.range (n + 1),
        n.choose j •
          (ChernClass.homogeneous δ f j (value δ f classes E₁ j) *
            ChernClass.homogeneous δ f (n - j) (value δ f classes E₂ (n - j))) := sorry

end AlgebraicGeometry.ChernPolynomial.Newton
