/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Nonnegative.Rational
public import stacks_project.Chap42.Lemma_42_35_4_Additive
public import Mathlib.LinearAlgebra.TensorProduct.Map

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Nonnegative

variable {S : Scheme.{u}} (δ : S → ℤ) [UniversallyCatenary S] [IsDimensionFunction δ]
variable {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]

/-- The integral-first rationalization of a nonnegative homogeneous bivariant degree. -/
abbrev RationalDegree (f : X ⟶ Y) (p : ℕ) : Type (u + 1) :=
  TensorProduct ℤ (BivariantClass δ f (p : ℤ)) ℚ

/-- A rational homogeneous degree is the integral-first tensor product over the integers. -/
theorem rationalDegree_def (f : X ⟶ Y) (p : ℕ) :
    RationalDegree δ f p = TensorProduct ℤ (BivariantClass δ f (p : ℤ)) ℚ := rfl

/-- The product of all rationalized nonnegative homogeneous bivariant degrees. -/
abbrev RationalCompletion (f : X ⟶ Y) : Type (u + 1) :=
  ∀ p : ℕ, RationalDegree δ f p

/-- The rational completion is the dependent product of its homogeneous degrees. -/
theorem rationalCompletion_def (f : X ⟶ Y) :
    RationalCompletion δ f = (∀ p : ℕ, RationalDegree δ f p) := rfl

/-- Completed rational bivariant classes agree if their components agree. -/
@[ext]
theorem RationalCompletion.ext {f : X ⟶ Y} {a b : RationalCompletion δ f}
    (h : ∀ p, a p = b p) : a = b := funext h

/-- The identity on integral classes induces an equivalence from their inferred
additive rationalization to their explicit pointwise rationalization. -/
def canonicalDegreeEquiv (f : X ⟶ Y) (p : ℕ) :
    RationalDegree δ f p ≃ₗ[ℤ] Rational.Degree δ f p :=
  @TensorProduct.congr ℤ ℤ inferInstance inferInstance (RingHom.id ℤ)
    (BivariantClass δ f (p : ℤ)) ℚ (BivariantClass δ f (p : ℤ)) ℚ
    inferInstance inferInstance
    (pointwiseAddCommGroup δ f (p : ℤ)).toAddCommMonoid inferInstance
    inferInstance inferInstance
    (@AddCommGroup.toIntModule _ (pointwiseAddCommGroup δ f (p : ℤ))) inferInstance
    (RingHom.id ℤ) inferInstance inferInstance
    (@AddEquiv.toIntLinearEquiv _ _
      (instAddCommGroup δ f (p : ℤ)) (pointwiseAddCommGroup δ f (p : ℤ))
      inferInstance (@AddCommGroup.toIntModule _ (pointwiseAddCommGroup δ f (p : ℤ)))
      { toFun := id
        invFun := id
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl })
    (LinearEquiv.refl ℤ ℚ)

/-- The rationalization equivalence preserves the pure tensor of an integral class
and a rational coefficient. -/
theorem canonicalDegreeEquiv_tmul (f : X ⟶ Y) (p : ℕ)
    (c : BivariantClass δ f (p : ℤ)) (q : ℚ) :
    canonicalDegreeEquiv δ f p (TensorProduct.tmul ℤ c q) =
      Rational.tensor δ f p c q := rfl

end AlgebraicGeometry.BivariantClass.Nonnegative
