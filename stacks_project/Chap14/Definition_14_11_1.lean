/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
import StacksCheckRecall

/-!
@stack 0175
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

variable (U : SSet.{u}) (n : ℕ)

/- Definition 14.11.1 (1): an `n`-simplex of `U` is an element of its degree-`n` term. -/
@[stacks 0175 "Definition 14.11.1 (1)"]
#check (U _⦋n⦌)

variable (x : U _⦋n + 1⦌) (y : U _⦋n⦌) (i : Fin (n + 2))

/- Definition 14.11.1 (2): `y` is the `i`th face of `x` when `U.δ i x = y`. -/
@[stacks 0175 "Definition 14.11.1 (2)"]
#check (U.δ i x = y)

variable (x' : U _⦋n⦌) (z : U _⦋n + 1⦌) (j : Fin (n + 1))

/- Definition 14.11.1 (3): `z` is the `j`th degeneracy of `x'` when `z = U.σ j x'`. -/
@[stacks 0175 "Definition 14.11.1 (3)"]
#check (z = U.σ j x')

/- Definition 14.11.1 (4): a positive-degree simplex is degenerate exactly when it lies in the
range of one of the elementary degeneracy maps. -/
@[stacks 0175 "Definition 14.11.1 (4)"]
#check (SSet.degenerate_eq_iUnion_range_σ U (n := n) :
  U.degenerate (n + 1) =
    ⋃ k : Fin (n + 1), Set.range (U.σ k))

/- The canonical lower-degree epimorphism characterization is a useful strengthening. -/
#check (SSet.mem_degenerate_iff U x')
