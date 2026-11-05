/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Matrix.Module
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Simple standard modules over full matrix rings

This leaf owns the elementary matrix-module fact independently of central simple algebra theory.
-/

@[expose] public section

open scoped Matrix.Module

universe u v

namespace IsSimpleModule

variable {K : Type u} [DivisionRing K]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The standard left module `ι → K` over the full matrix ring `Matrix ι ι K` is simple.
The explicit element `i` records the nonemptiness needed to recover every coordinate from a
nonzero vector. -/
theorem matrix_fun (i : ι) :
    IsSimpleModule (Matrix ι ι K) (ι → K) := by
  classical
  letI : Nonempty ι := ⟨i⟩
  refine isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨inferInstance, ?_⟩
  intro x hx y
  have hx' : ¬ ∀ j, x j = 0 := fun h ↦ hx (funext h)
  obtain ⟨j, hj⟩ := not_forall.mp hx'
  let M : Matrix ι ι K := fun r c ↦ if c = j then y r * (x j)⁻¹ else 0
  refine ⟨M, ?_⟩
  change M • x = y
  ext r
  simp [M, Matrix.Module.smul_apply, smul_eq_mul, mul_assoc, hj]

/-- The standard module over `Matrix (Fin n) (Fin n) K` is simple whenever `n` is positive.
This is the `Fin n` convenience specialization of `matrix_fun`. -/
theorem matrix_fin_fun {n : ℕ} (hn : 1 ≤ n) :
    IsSimpleModule (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
  matrix_fun ⟨0, hn⟩

end IsSimpleModule
