/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension

/-! # Integer bounds on the dimension of algebraic spaces -/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An integer upper bound on dimension; a negative bound requires dimension bottom. -/
def dimensionLEInt {S : Scheme.{u}} (X : AlgebraicSpace S) (d : ℤ) : Prop :=
  match d with
  | .ofNat n => dimension X ≤ n
  | .negSucc _ => dimension X = ⊥

/-- A nonnegative integer bound is the corresponding natural-number dimension bound. -/
@[simp] theorem dimensionLEInt_ofNat {S : Scheme.{u}} (X : AlgebraicSpace S) (n : ℕ) :
    dimensionLEInt X (Int.ofNat n) ↔ dimension X ≤ n := Iff.rfl

/-- A negative integer bound is equivalent to dimension bottom. -/
@[simp] theorem dimensionLEInt_negSucc {S : Scheme.{u}} (X : AlgebraicSpace S) (n : ℕ) :
    dimensionLEInt X (Int.negSucc n) ↔ dimension X = ⊥ := Iff.rfl

end AlgebraicGeometry.AlgebraicSpace
