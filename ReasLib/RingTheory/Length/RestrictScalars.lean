/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Length
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Length under restriction of scalars

@stack 00IX

This leaf owns the monotonicity of module length under a compatible restriction of scalars.
The equality for a surjective scalar map remains the canonical Mathlib theorem
`Module.length_eq_of_surjective`.
-/

@[expose] public section

universe u v w

namespace Module

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [Ring S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- Lemma 10.52.5 (1) (Tag 00IX): restriction of scalars cannot decrease the length of a
module. -/
@[stacks 00IX "(1), length under restriction of scalars"]
theorem length_le_restrictScalars : length S M ≤ length R M := sorry

end Module
