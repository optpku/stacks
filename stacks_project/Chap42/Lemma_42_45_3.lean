/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ChernCharacter.Tensor

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators MonoidalCategory

universe u

/- Lemma 42.45.3 (1): the degree-`n` component of the Chern character of a tensor product
is the convolution of the components of the Chern characters of its factors. -/
@[stacks 0F9D]
#check
  (AlgebraicGeometry.ChernClass.Theory.characterComponent_tensor :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (f : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType f]
      (classes : AlgebraicGeometry.ChernClass.Theory δ f) (E₁ E₂ : X.Modules)
      [E₁.IsFiniteLocallyFree] [E₂.IsFiniteLocallyFree] (n : ℕ),
      AlgebraicGeometry.ChowCohomology.Nonnegative.rationalHomogeneous δ f n
          (AlgebraicGeometry.ChernClass.Theory.characterComponent
            δ f classes (E₁ ⊗ E₂) n) =
        ∑ j ∈ Finset.range (n + 1),
          AlgebraicGeometry.ChowCohomology.Nonnegative.rationalHomogeneous δ f j
              (AlgebraicGeometry.ChernClass.Theory.characterComponent δ f classes E₁ j) *
            AlgebraicGeometry.ChowCohomology.Nonnegative.rationalHomogeneous δ f (n - j)
              (AlgebraicGeometry.ChernClass.Theory.characterComponent
                δ f classes E₂ (n - j)))

/- Lemma 42.45.3 (2): the degree-`n` Newton value of a tensor product is the binomial
convolution of the Newton values of its factors in `Aⁿ(X)`. -/
@[stacks 0F9D]
#check
  (AlgebraicGeometry.ChernPolynomial.Newton.value_tensor :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (f : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType f]
      (classes : AlgebraicGeometry.ChernClass.Theory δ f) (E₁ E₂ : X.Modules)
      [E₁.IsFiniteLocallyFree] [E₂.IsFiniteLocallyFree] (n : ℕ),
      AlgebraicGeometry.ChernClass.homogeneous δ f n
          (AlgebraicGeometry.ChernPolynomial.Newton.value δ f classes (E₁ ⊗ E₂) n) =
        ∑ j ∈ Finset.range (n + 1),
          n.choose j •
            (AlgebraicGeometry.ChernClass.homogeneous δ f j
                (AlgebraicGeometry.ChernPolynomial.Newton.value δ f classes E₁ j) *
              AlgebraicGeometry.ChernClass.homogeneous δ f (n - j)
                (AlgebraicGeometry.ChernPolynomial.Newton.value
                  δ f classes E₂ (n - j))))
