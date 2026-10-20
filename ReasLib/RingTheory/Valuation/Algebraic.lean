/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Valuation subrings in algebraic field extensions

@stack 0AAV

This leaf records the contraction criterion for valuation subrings along an
algebraic extension of fields.  The contracted valuation subring itself is the
canonical `ValuationSubring.comap`; only the non-field conclusion needs an
additional theorem.
-/

@[expose] public section

universe u v

namespace ValuationSubring

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Lemma 10.50.8: if `L / K` is algebraic and a valuation subring `B` of `L`
is not a field, then its contraction to `K` is not a field. -/
@[stacks 0AAV "non-field contraction along an algebraic extension"]
theorem not_isField_comap_algebraMap_of_isAlgebraic [Algebra.IsAlgebraic K L]
    (B : ValuationSubring L) (hB : ¬ IsField B) :
    ¬ IsField (B.comap (algebraMap K L)) := sorry

end ValuationSubring
