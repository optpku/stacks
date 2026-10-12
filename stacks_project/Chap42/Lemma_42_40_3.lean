/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap42.Lemma_42_40_2

@[expose] public section

open CategoryTheory
open scoped BigOperators

universe u

namespace AlgebraicGeometry.ChernClass.Theory

/- Lemma 42.40.3: For a short exact sequence `0 ⟶ E₁ ⟶ E ⟶ E₂ ⟶ 0` whose
endpoints are finite locally free of ranks `r₁` and `r₂`, the total Chern class
of `E` is the product of the total Chern classes of `E₁` and `E₂`. -/
@[stacks 02UI] #check
  (AlgebraicGeometry.ChernClass.Theory.total_eq_mul_of_shortExact :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      (classes : Theory δ p) (C : ShortComplex X.Modules) (r₁ r₂ : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank r₁ C.X₁]
      [Scheme.Modules.IsFiniteLocallyFreeOfRank r₂ C.X₃]
      (hC : C.ShortExact),
      (∑ i : Fin (r₁ + r₂ + 1),
        ChernClass.homogeneous δ p (i : ℕ) (classes.component C.X₂ i)) =
        (∑ i : Fin (r₁ + 1),
          ChernClass.homogeneous δ p (i : ℕ) (classes.component C.X₁ i)) *
        (∑ i : Fin (r₂ + 1),
          ChernClass.homogeneous δ p (i : ℕ) (classes.component C.X₃ i)))

end AlgebraicGeometry.ChernClass.Theory
