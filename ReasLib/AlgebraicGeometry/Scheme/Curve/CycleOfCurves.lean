/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Pairwise
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension

/-!
# Cycles of curves

A finite cyclic incidence of pairwise distinct integral dimension-one closed
subschemes and pairwise distinct closed points on a scheme.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite cyclic incidence of pairwise distinct integral dimension-one closed
subschemes `C` and pairwise distinct closed points `x` on a scheme `X`. The
cyclic successor on `Fin n` is `finRotate n`. -/
def IsCycleOfCurves {X : Scheme.{u}} {n : ℕ}
    (C : Fin n → X.IdealSheafData) (x : Fin n → X) : Prop :=
  2 ≤ n ∧
    (Pairwise fun i j ↦ C i ≠ C j) ∧
    (∀ i, IsIntegral (C i).subscheme) ∧
    (∀ i, topologicalKrullDim (C i).subscheme = 1) ∧
    (∀ i, x i ∈ closedPoints X) ∧
    (Pairwise fun i j ↦ x i ≠ x j) ∧
    ∀ i, x i ∈ (C i).support ∧ x i ∈ (C (finRotate n i)).support

/-- `IsCycleOfCurves C x` holds exactly when the cycle-size, distinctness,
integrality, dimension, closed-point, and cyclic-incidence conditions hold. -/
theorem isCycleOfCurves_iff {X : Scheme.{u}} {n : ℕ}
    (C : Fin n → X.IdealSheafData) (x : Fin n → X) :
    IsCycleOfCurves C x ↔
      2 ≤ n ∧
        (Pairwise fun i j ↦ C i ≠ C j) ∧
        (∀ i, IsIntegral (C i).subscheme) ∧
        (∀ i, topologicalKrullDim (C i).subscheme = 1) ∧
        (∀ i, x i ∈ closedPoints X) ∧
        (Pairwise fun i j ↦ x i ≠ x j) ∧
        ∀ i, x i ∈ (C i).support ∧ x i ∈ (C (finRotate n i)).support := sorry

end AlgebraicGeometry.Scheme
