/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Basic

/-!
# Determinantal ideals and scalar left inverses

This leaf records the rectangular-matrix criterion relating maximal minors to
a left inverse up to a scalar.  It is independent of any presentation or
Jacobian application.
-/

@[expose] public section

universe u v

namespace Matrix.MinorIdeal

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι]
variable {m : ℕ}

/-- Membership in the maximal-minor ideal produces a left inverse up to the
given scalar. -/
@[stacks 07DQ]
theorem exists_mul_eq_smul_one (A : Matrix ι (Fin m) R) {f : R}
    (hf : f ∈ Matrix.minorIdeal m A) :
    ∃ B : Matrix (Fin m) ι R, B * A = f • 1 := sorry

/-- A scalar left inverse forces the corresponding power of the scalar to
belong to the maximal-minor ideal. -/
@[stacks 07DQ]
theorem pow_mem_of_mul_eq_smul_one (A : Matrix ι (Fin m) R) {f : R}
    (B : Matrix (Fin m) ι R) (hBA : B * A = f • 1) :
    f ^ m ∈ Matrix.minorIdeal m A := sorry

/-- Existential form of `pow_mem_of_mul_eq_smul_one`. -/
@[stacks 07DQ "existential scalar left-inverse power"]
theorem pow_mem_of_exists_mul_eq_smul_one (A : Matrix ι (Fin m) R) {f : R}
    (hBA : ∃ B : Matrix (Fin m) ι R, B * A = f • 1) :
    f ^ m ∈ Matrix.minorIdeal m A := sorry

end Matrix.MinorIdeal
