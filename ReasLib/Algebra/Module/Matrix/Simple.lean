/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
    IsSimpleModule (Matrix ι ι K) (ι → K) := sorry

/-- The standard module over `Matrix (Fin n) (Fin n) K` is simple whenever `n` is positive.
This is the `Fin n` convenience specialization of `matrix_fun`. -/
theorem matrix_fin_fun {n : ℕ} (hn : 1 ≤ n) :
    IsSimpleModule (Matrix (Fin n) (Fin n) K) (Fin n → K) := sorry

end IsSimpleModule
