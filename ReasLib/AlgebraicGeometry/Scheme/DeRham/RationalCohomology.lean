/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CanonicalAction
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Cohomology.Pullback
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Ring.MinimalAxioms
public import Mathlib.Data.Finset.NatAntidiagonal

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Rational

/-- The relative de Rham cohomology over `ℚ` in nonnegative even degree `2 * degree`. -/
abbrev evenCohomology (X : SchemeOverField (ULift.{u} ℚ)) (degree : ℕ) :
    ModuleCat.{u} (ULift.{u} ℚ) :=
  cohomologyOverAffineBase X.hom (2 * (degree : ℤ))

/-- Completed even relative de Rham cohomology is the product of its even-degree groups. -/
def CompletedEven (X : SchemeOverField (ULift.{u} ℚ)) : Type u :=
  (degree : ℕ) → evenCohomology X degree

/-- The sum of the even integer degrees of two natural indices is the degree of their sum. -/
theorem evenDegree_add (first second : ℕ) :
    2 * (first : ℤ) + 2 * (second : ℤ) = 2 * ((first + second : ℕ) : ℤ) := sorry

/-- The canonical cup product of two even-degree classes, transported to the summed index. -/
def cup (X : SchemeOverField (ULift.{u} ℚ)) (first second : ℕ)
    (ξ : evenCohomology X first) (η : evenCohomology X second) :
    evenCohomology X (first + second) :=
  (eqToHom (congrArg (cohomology X.hom) (evenDegree_add first second))).hom
    ((CanonicalAction.cupMorphism X.hom (2 * (first : ℤ)) (2 * (second : ℤ))).hom
      (ξ ⊗ₜ η))

namespace CompletedEven

variable (X : SchemeOverField (ULift.{u} ℚ))

/-- Completed even cohomology has the pointwise additive group structure. -/
instance instAddCommGroup : AddCommGroup (CompletedEven X) :=
  inferInstanceAs (AddCommGroup ((degree : ℕ) → evenCohomology X degree))

/-- The completed cohomological unit has the canonical unit in degree zero and zero elsewhere. -/
def one : CompletedEven X
  | 0 => ClassAction.cohomologyOneCanonical X.hom
  | degree + 1 => 0

/-- Multiplication in completed even cohomology is finite cup-product convolution. -/
def mul (ξ η : CompletedEven X) : CompletedEven X :=
  fun degree ↦ ∑ component ∈ (Finset.antidiagonal degree).attach,
    (eqToHom (congrArg (evenCohomology X)
      (Finset.mem_antidiagonal.mp component.property))).hom
        (cup X component.val.1 component.val.2 (ξ component.val.1) (η component.val.2))

/-- The canonical degree-zero cohomological unit defines the completed unit operation. -/
instance instOne : One (CompletedEven X) := ⟨one X⟩

/-- Finite cup-product convolution defines the completed multiplication operation. -/
instance instMul : Mul (CompletedEven X) := ⟨mul X⟩

/-- Cup-product convolution in completed even cohomology is associative. -/
theorem mul_assoc (ξ η ζ : CompletedEven X) : (ξ * η) * ζ = ξ * (η * ζ) := sorry

/-- Cup-product convolution in even degrees is commutative. -/
theorem mul_comm (ξ η : CompletedEven X) : ξ * η = η * ξ := sorry

/-- The degree-zero cohomological unit is a left unit for cup-product convolution. -/
theorem one_mul (ξ : CompletedEven X) : 1 * ξ = ξ := sorry

/-- Cup-product convolution distributes over pointwise addition on the left. -/
theorem left_distrib (ξ η ζ : CompletedEven X) : ξ * (η + ζ) = ξ * η + ξ * ζ := sorry

/-- Completed even relative de Rham cohomology is a commutative ring under cup convolution. -/
instance instCommRing : CommRing (CompletedEven X) :=
  CommRing.ofMinimalAxioms _root_.add_assoc _root_.zero_add _root_.neg_add_cancel
    (mul_assoc X) (mul_comm X) (one_mul X) (left_distrib X)

/-- The ring unit has its canonical degree-zero component and vanishing positive components. -/
theorem one_apply (degree : ℕ) :
    (1 : CompletedEven X) degree =
      match degree with
      | 0 => ClassAction.cohomologyOneCanonical X.hom
      | degree + 1 => 0 := sorry

/-- Each component of ring multiplication is the finite convolution of canonical cup products. -/
theorem mul_apply (ξ η : CompletedEven X) (degree : ℕ) :
    (ξ * η) degree = ∑ component ∈ (Finset.antidiagonal degree).attach,
      (eqToHom (congrArg (evenCohomology X)
        (Finset.mem_antidiagonal.mp component.property))).hom
          (cup X component.val.1 component.val.2 (ξ component.val.1) (η component.val.2)) := sorry

end CompletedEven

/-- A morphism of schemes over `ℚ` determines a square over the identity of the base. -/
theorem pullbackCommSq {X Y : SchemeOverField (ULift.{u} ℚ)} (f : X ⟶ Y) :
    CommSq f.left X.hom Y.hom (𝟙 _) := sorry

/-- Pullback on completed even relative de Rham cohomology is the canonical componentwise
derived pullback over the fixed rational base. -/
def pullback {X Y : SchemeOverField (ULift.{u} ℚ)} (f : X ⟶ Y)
    (ξ : CompletedEven Y) : CompletedEven X :=
  fun degree ↦ (Cohomology.restrictedPullback (pullbackCommSq f) (2 * (degree : ℤ))
    (hPull := RingedSite.Hom.modulePushforwardToDerived.hasRightDerived
      (Cohomology.coefficientHom (pullbackCommSq f)))).hom (ξ degree)

end AlgebraicGeometry.Scheme.DeRham.Rational
