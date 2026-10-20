/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Support of the self-module

@stack 00N9

The regular module has full prime support.  This small owner is useful whenever
a ring-level statement is obtained by specializing a module theorem to `M = R`.
-/

@[expose] public section

universe u

namespace Module

variable {R : Type u} [CommRing R]

/-- The regular `R`-module is supported at every prime of `R`. -/
@[stacks 00N9 "full support of the regular module"]
theorem support_self_eq_univ : support R R = Set.univ := sorry

end Module
