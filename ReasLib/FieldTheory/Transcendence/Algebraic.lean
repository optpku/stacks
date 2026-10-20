/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

universe u v

namespace Algebra

/-- An algebraic extension of fields preserves transcendence degree over a compatible base field. -/
theorem trdeg_eq_of_isAlgebraic
    {k : Type u} {K : Type v} {K' : Type v}
    [Field k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K']
    [IsScalarTower k K K'] [Algebra.IsAlgebraic K K'] :
    trdeg k K = trdeg k K' := sorry

end Algebra
