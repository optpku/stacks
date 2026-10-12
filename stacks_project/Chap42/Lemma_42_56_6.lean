/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Adams.ChernClass
import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Adams.ChernCharacter

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 42.56.6 (1): the second Adams operation multiplies the degree-`i`
Chern-class component of every vector-bundle `K₀` class by `2 ^ i`. -/
@[stacks 0FEN] #check
  (AlgebraicGeometry.Scheme.VectorBundleK0.totalChernClass_adamsTwo_apply :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      (classes : AlgebraicGeometry.ChernClass.Theory δ p)
      (α : AlgebraicGeometry.Scheme.VectorBundleK0 X) (i : ℕ),
      AlgebraicGeometry.Scheme.VectorBundleK0.totalChernClass δ p classes
          (AlgebraicGeometry.Scheme.VectorBundleK0.adamsTwo X α) i =
        (2 ^ i : ℕ) •
          AlgebraicGeometry.Scheme.VectorBundleK0.totalChernClass δ p classes α i)

/- Lemma 42.56.6 (2): the second Adams operation multiplies the degree-`i`
Chern-character component of every vector-bundle `K₀` class by `2 ^ i`. -/
@[stacks 0FEN] #check
  (AlgebraicGeometry.Scheme.VectorBundleK0.chernCharacter_adamsTwo_apply :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      (classes : AlgebraicGeometry.ChernClass.Theory δ p)
      (α : AlgebraicGeometry.Scheme.VectorBundleK0 X) (i : ℕ),
      AlgebraicGeometry.Scheme.VectorBundleK0.chernCharacter δ p classes
          (AlgebraicGeometry.Scheme.VectorBundleK0.adamsTwo X α) i =
        (2 ^ i : ℕ) •
          AlgebraicGeometry.Scheme.VectorBundleK0.chernCharacter δ p classes α i)
