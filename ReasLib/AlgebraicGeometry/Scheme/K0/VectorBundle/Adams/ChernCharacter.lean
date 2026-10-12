/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Adams
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.ChernCharacter

/-!
# The second Adams operation and the Chern character

The second Adams operation scales each component of the Chern character by the
corresponding power of two.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.VectorBundleK0

/-- The second Adams operation multiplies the degree-`i` Chern-character component
of a vector-bundle `K₀` class by `2 ^ i`. -/
theorem chernCharacter_adamsTwo_apply {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : ChernClass.Theory δ p) (α : VectorBundleK0 X) (i : ℕ) :
    chernCharacter δ p classes (adamsTwo X α) i =
      (2 ^ i : ℕ) • chernCharacter δ p classes α i := sorry

end AlgebraicGeometry.Scheme.VectorBundleK0
