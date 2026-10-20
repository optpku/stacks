/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Projective Modules

This root owns the canonical predicate `Module.FiniteProjective` and its two
elementary projections. Specialized closure, base-change, local-ring, and
descent results live in direct-import child leaves.
-/

@[expose] public section

universe u v

namespace Module

/-- An `R`-module is finite projective when it is both finite and projective. -/
@[stacks 00JH "finite projective modules"]
def FiniteProjective (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Prop :=
  Module.Finite R M ∧ Module.Projective R M

namespace FiniteProjective

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Finite projectivity includes finite generation. -/
@[stacks 00JH "finite projective modules are finite"]
theorem finite (h : Module.FiniteProjective R M) : Module.Finite R M :=
  h.1

/-- Finite projectivity includes projectivity. -/
@[stacks 00JH "finite projective modules are projective"]
theorem projective (h : Module.FiniteProjective R M) : Module.Projective R M :=
  h.2

end FiniteProjective

end Module
