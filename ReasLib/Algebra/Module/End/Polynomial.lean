/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Polynomial evaluations of module endomorphisms

This leaf records a cardinality obstruction to every monic polynomial in an
endomorphism being invertible.

@stack 00FT
-/

@[expose] public section

open Cardinal Polynomial

universe u v

namespace Module.End

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V] [Nontrivial V]

/-- If a nonzero `k`-vector space has dimension strictly smaller than the
cardinality of `k`, every endomorphism admits a monic polynomial evaluation
which is not a unit.

This is Lemma 10.35.10 of the Stacks project. -/
@[stacks 00FT]
theorem exists_monic_aeval_not_isUnit_of_rank_lt_cardinal
    (T : Module.End k V)
    (hV : lift.{max u v} (Module.rank k V) < lift.{max u v} (#k)) :
    ∃ P : k[X], P.Monic ∧ ¬ IsUnit (aeval T P) := sorry

end Module.End
