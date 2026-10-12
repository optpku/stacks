/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v

namespace Algebra

/-- Exercise 111.20.1: if `K'/K/k` is a tower of field extensions and `K'` is algebraic over `K`,
then `trdeg k K = trdeg k K'`. -/
@[stacks 077F]
theorem trdeg_eq_of_isAlgebraic
    {k : Type u} {K : Type v} {K' : Type v}
    [Field k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K']
    [IsScalarTower k K K'] [Algebra.IsAlgebraic K K'] :
    trdeg k K = trdeg k K' := sorry

end Algebra
