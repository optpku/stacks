/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_35_4_Additive
public import Mathlib.LinearAlgebra.TensorProduct.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BivariantClass.Nonnegative

variable {S : Scheme.{u}} (δ : S → ℤ) [UniversallyCatenary S] [IsDimensionFunction δ]
variable {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]

/-- The rationalization of a nonnegative homogeneous bivariant degree. -/
abbrev RationalDegree (f : X ⟶ Y) (p : ℕ) : Type (u + 1) :=
  TensorProduct ℤ (BivariantClass δ f (p : ℤ)) ℚ

/-- `RationalDegree` is the tensor product of the integral bivariant degree with `ℚ`. -/
theorem rationalDegree_def (f : X ⟶ Y) (p : ℕ) :
    RationalDegree δ f p = TensorProduct ℤ (BivariantClass δ f (p : ℤ)) ℚ := sorry

/-- The completed product of all rationalized nonnegative bivariant degrees. -/
abbrev RationalCompletion (f : X ⟶ Y) : Type (u + 1) :=
  ∀ p : ℕ, RationalDegree δ f p

/-- `RationalCompletion` is the dependent product of its rational homogeneous degrees. -/
theorem rationalCompletion_def (f : X ⟶ Y) :
    RationalCompletion δ f = (∀ p : ℕ, RationalDegree δ f p) := sorry

namespace RationalCompletion

/-- Two completed rational bivariant classes are equal when all components agree. -/
@[ext]
theorem ext {f : X ⟶ Y} {a b : RationalCompletion δ f}
    (h : ∀ p, a p = b p) : a = b := sorry

end RationalCompletion

end AlgebraicGeometry.BivariantClass.Nonnegative
