/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Flat Finite Products

This leaf owns the finite-product closure property for flat modules.  It is
separate from direct sums because arbitrary products need not be flat.
-/

universe u v w

namespace Module.Flat

/-- A finite dependent product of flat modules is flat. -/
@[stacks 034Z "finite product of flat modules"]
theorem pi
    {R : Type u} {ι : Type v} {M : ι -> Type w} [CommSemiring R] [Finite ι]
    [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]
    [forall i, Module.Flat R (M i)] :
    Module.Flat R (forall i, M i) := sorry

end Module.Flat
