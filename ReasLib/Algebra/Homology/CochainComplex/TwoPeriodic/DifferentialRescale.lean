/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic
public import ReasLib.Algebra.Homology.HomologicalComplex.DifferentialRescale.Linear

/-!
# Scaling Differentials of Two-Periodic Endomorphisms

This file constructs the two ways to scale one differential of a two-periodic endomorphism
and compares them with linear rescaling of the associated cochain complex.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R]

/-- Scaling the degree-zero differential preserves its zero composite with the degree-one
differential. -/
theorem smulD₀_d₀_d₁ (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (x : R) :
    (x • K.d₀) ≫ K.d₁ = 0 := by
  simp [K.d₀_d₁]

/-- Scaling the degree-zero differential preserves the zero composite in the other order. -/
theorem smulD₀_d₁_d₀ (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (x : R) :
    K.d₁ ≫ (x • K.d₀) = 0 := by
  simp [K.d₁_d₀]

/-- Scale the degree-zero differential of a two-periodic endomorphism by `x`. -/
def smulD₀ (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (x : R) :
    TwoPeriodicEndomorphism (ModuleCat R) where
  X := K.X
  d₀ := x • K.d₀
  d₁ := K.d₁
  d₀_d₁ := smulD₀_d₀_d₁ K x
  d₁_d₀ := smulD₀_d₁_d₀ K x

/-- Scaling the degree-one differential preserves its zero composite with the degree-zero
differential. -/
theorem smulD₁_d₀_d₁ (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (x : R) :
    K.d₀ ≫ (x • K.d₁) = 0 := by
  simp [K.d₀_d₁]

/-- Scaling the degree-one differential preserves the zero composite in the other order. -/
theorem smulD₁_d₁_d₀ (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (x : R) :
    (x • K.d₁) ≫ K.d₀ = 0 := by
  simp [K.d₁_d₀]

/-- Scale the degree-one differential of a two-periodic endomorphism by `x`. -/
def smulD₁ (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (x : R) :
    TwoPeriodicEndomorphism (ModuleCat R) where
  X := K.X
  d₀ := K.d₀
  d₁ := x • K.d₁
  d₀_d₁ := smulD₁_d₀_d₁ K x
  d₁_d₀ := smulD₁_d₁_d₀ K x

/-- Scaling the degree-zero differential leaves the underlying object unchanged. -/
@[simp]
theorem smulD₀_X (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (x : R) :
    (smulD₀ K x).X = K.X := rfl

/-- The degree-zero differential of `smulD₀ K x` is `x • K.d₀`. -/
@[simp]
theorem smulD₀_d₀ (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (x : R) :
    (smulD₀ K x).d₀ = x • K.d₀ := rfl

/-- The degree-one differential of `smulD₀ K x` is unchanged. -/
@[simp]
theorem smulD₀_d₁ (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (x : R) :
    (smulD₀ K x).d₁ = K.d₁ := rfl

/-- Scaling the degree-one differential leaves the underlying object unchanged. -/
@[simp]
theorem smulD₁_X (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (x : R) :
    (smulD₁ K x).X = K.X := rfl

/-- The degree-zero differential of `smulD₁ K x` is unchanged. -/
@[simp]
theorem smulD₁_d₀ (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (x : R) :
    (smulD₁ K x).d₀ = K.d₀ := rfl

/-- The degree-one differential of `smulD₁ K x` is `x • K.d₁`. -/
@[simp]
theorem smulD₁_d₁ (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (x : R) :
    (smulD₁ K x).d₁ = x • K.d₁ := rfl

/-- Scaling `d₀` agrees with linear rescaling of the associated cochain complex in degree
zero. -/
theorem smulD₀_toCochainComplex (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (x : R) :
    (smulD₀ K x).toCochainComplex =
      HomologicalComplex.Rescale.ofLinear K.toCochainComplex
        (fun i : ZMod 2 ↦ if i = 0 then x else 1) := by
  apply HomologicalComplex.ext
  case h_X => rfl
  case h_d =>
    intro i j hij
    obtain rfl : i + 1 = j := hij
    dsimp only [toCochainComplex, smulD₀, HomologicalComplex.Rescale.ofLinear,
      HomologicalComplex.rescale, HomologicalComplex.Rescale.ofLinear.scalar,
      CatCenter.smul_eq, Linear.scalarCenter, CatCenter.app]
    simp only [CochainComplex.of_d]
    by_cases hi : i = 0 <;> simp [hi]

/-- Scaling `d₁` agrees with linear rescaling of the associated cochain complex in degree
one. -/
theorem smulD₁_toCochainComplex (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (x : R) :
    (smulD₁ K x).toCochainComplex =
      HomologicalComplex.Rescale.ofLinear K.toCochainComplex
        (fun i : ZMod 2 ↦ if i = 1 then x else 1) := by
  apply HomologicalComplex.ext
  case h_X => rfl
  case h_d =>
    intro i j hij
    obtain rfl : i + 1 = j := hij
    dsimp only [toCochainComplex, smulD₁, HomologicalComplex.Rescale.ofLinear,
      HomologicalComplex.rescale, HomologicalComplex.Rescale.ofLinear.scalar,
      CatCenter.smul_eq, Linear.scalarCenter, CatCenter.app]
    simp only [CochainComplex.of_d]
    have hi : i = 0 ∨ i = 1 := by
      exact (by decide : ∀ i : ZMod 2, i = 0 ∨ i = 1) i
    rcases hi with hi | hi <;> simp [hi]

end CategoryTheory.TwoPeriodicEndomorphism
