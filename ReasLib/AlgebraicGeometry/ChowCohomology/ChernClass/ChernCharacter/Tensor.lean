/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ChernCharacter
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton.Tensor
public import ReasLib.AlgebraicGeometry.ChowCohomology.Rational

@[expose] public section

open CategoryTheory
open scoped BigOperators MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Theory

/-- The degree-`n` component of the Chern character of a tensor product is the
convolution of the components of the Chern characters of its factors. -/
theorem characterComponent_tensor {S X : Scheme.{u}} (δ : S → ℤ) (f : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType f]
    (classes : Theory δ f) (E₁ E₂ : X.Modules)
    [E₁.IsFiniteLocallyFree] [E₂.IsFiniteLocallyFree] (n : ℕ) :
    ChowCohomology.Nonnegative.rationalHomogeneous δ f n
        (characterComponent δ f classes (E₁ ⊗ E₂) n) =
      ∑ j ∈ Finset.range (n + 1),
        ChowCohomology.Nonnegative.rationalHomogeneous δ f j
            (characterComponent δ f classes E₁ j) *
          ChowCohomology.Nonnegative.rationalHomogeneous δ f (n - j)
            (characterComponent δ f classes E₂ (n - j)) := sorry

end AlgebraicGeometry.ChernClass.Theory
