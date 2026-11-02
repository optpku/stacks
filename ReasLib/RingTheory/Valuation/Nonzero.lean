/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The valuation of nonzero elements of a valuation ring

@stack 00IF

This leaf restricts the canonical fraction-field valuation of a valuation
ring to its nonzero elements.  The codomain is the unit group of the value
monoid, matching the source's multiplicative value group.
-/

@[expose] public section

universe u

open Valuation

namespace ValuationRing

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

/-- The canonical valuation of a nonzero element of a valuation ring, valued
in the unit group of its fraction-field value monoid. -/
@[stacks 00IF "nonzero valuation"]
noncomputable def nonzeroValuation (a : {a : A // a ≠ 0}) :
    (ValueGroup A (FractionRing A))ˣ :=
  Units.mk0
    (valuation A (FractionRing A) (algebraMap A (FractionRing A) (a : A)))
    ((Valuation.ne_zero_iff (valuation A (FractionRing A))).2
      ((map_ne_zero_iff (algebraMap A (FractionRing A))
        (IsFractionRing.injective A (FractionRing A))).2 a.2))

/-- Coercing `nonzeroValuation` recovers the canonical valuation. -/
@[simp, stacks 00IF "coercion"]
theorem nonzeroValuation_coe (a : {a : A // a ≠ 0}) :
    ((nonzeroValuation A a : (ValueGroup A (FractionRing A))ˣ) :
        ValueGroup A (FractionRing A)) =
      valuation A (FractionRing A) (algebraMap A (FractionRing A) (a : A)) := rfl

/-- A nonzero element of the valuation ring has multiplicative value at most one. -/
@[simp, stacks 00IF "valuation-ring bound"]
theorem nonzeroValuation_le_one (a : {a : A // a ≠ 0}) :
    ((nonzeroValuation A a : (ValueGroup A (FractionRing A))ˣ) :
        ValueGroup A (FractionRing A)) ≤ 1 := by
  rw [nonzeroValuation_coe]
  exact (mem_integer_iff A (FractionRing A) _).2 ⟨(a : A), rfl⟩

/-- The additive normalization of `nonzeroValuation` is the canonical additive valuation. -/
@[simp, stacks 00IF "additive normalization"]
theorem nonzeroValuation_toAdd (a : {a : A // a ≠ 0}) :
    OrderDual.toDual
        (Additive.ofMul
          (((nonzeroValuation A a : (ValueGroup A (FractionRing A))ˣ) :
            ValueGroup A (FractionRing A)))) =
      Valuation.toAddValuation (valuation A (FractionRing A))
        (algebraMap A (FractionRing A) (a : A)) := rfl

/-- The additive value of a nonzero element of a valuation ring is nonnegative. -/
@[stacks 00IF "nonnegative additive value"]
theorem nonzeroValuation_toAdd_nonneg (a : {a : A // a ≠ 0}) :
    0 ≤ Valuation.toAddValuation (valuation A (FractionRing A))
      (algebraMap A (FractionRing A) (a : A)) := by
  change valuation A (FractionRing A) (algebraMap A (FractionRing A) (a : A)) ≤ 1
  exact nonzeroValuation_le_one A a

/-- Lemma 10.50.14 (1): a nonzero element has value one exactly when it is a unit. -/
@[stacks 00IF "(1)"]
theorem nonzeroValuation_eq_one_iff_isUnit (a : {a : A // a ≠ 0}) :
    nonzeroValuation A a = 1 ↔ IsUnit (a : A) := by
  have hv : (valuation A (FractionRing A)).Integers A := {
    hom_inj := IsFractionRing.injective A (FractionRing A)
    map_le_one x := (mem_integer_iff A (FractionRing A) _).2 ⟨x, rfl⟩
    exists_of_le_one {x} hx := (mem_integer_iff A (FractionRing A) x).1 hx }
  rw [← Units.val_eq_one, nonzeroValuation_coe]
  exact hv.isUnit_iff_valuation_eq_one.symm

/-- Lemma 10.50.14 (2): the nonzero valuation is multiplicative. -/
@[stacks 00IF "(2)"]
theorem nonzeroValuation_mul (a b : {a : A // a ≠ 0}) :
    nonzeroValuation A
        ⟨(a : A) * (b : A), mul_ne_zero a.2 b.2⟩ =
      nonzeroValuation A a * nonzeroValuation A b := by
  apply Units.ext
  simp only [Units.val_mul, nonzeroValuation_coe, map_mul]

/-- Lemma 10.50.14 (3): the nonzero valuation satisfies the ultrametric inequality. -/
@[stacks 00IF "(3)"]
theorem nonzeroValuation_add_le_max
    (a b : {a : A // a ≠ 0}) (hab : (a : A) + (b : A) ≠ 0) :
    nonzeroValuation A ⟨(a : A) + (b : A), hab⟩ ≤
      max (nonzeroValuation A a) (nonzeroValuation A b) := by
  apply Units.val_le_val.mp
  simpa only [Units.max_val, nonzeroValuation_coe, map_add] using
    (valuation A (FractionRing A)).map_add
      (algebraMap A (FractionRing A) (a : A)) (algebraMap A (FractionRing A) (b : A))

end ValuationRing
