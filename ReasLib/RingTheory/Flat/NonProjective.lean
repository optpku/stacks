/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Finiteness.Defs

@[expose] public section

universe u v

namespace Module

/-- Some commutative ring admits a finite flat module that is not projective. -/
theorem exists_finite_flat_not_projective :
    ∃ (R : Type u) (_ : CommRing R) (M : Type v) (_ : AddCommGroup M) (_ : Module R M),
      Module.Finite R M ∧ Flat R M ∧ ¬ Projective R M := sorry

end Module
