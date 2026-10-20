/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Basic
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Rank
public import ReasLib.RingTheory.Depth

/-!
# Buchsbaum--Eisenbud exactness criterion

@stack 00N1

The depth formulation is the reusable owner.  The regular-sequence statement
is retained as a source-facing companion without introducing a redundant
wrapper predicate.
-/

@[expose] public section

universe u

namespace FiniteFreeComplex

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {e : ℕ}

/-- Proposition 10.102.9: a bounded finite free complex is exact in positive degrees exactly
when each displayed differential has the expected exterior rank and sufficient depth in its
rank-minor ideal. -/
@[stacks 00N1 "Buchsbaum--Eisenbud depth criterion"]
theorem exactInPositiveDegrees_iff_rankMinorIdeal_depth
    (C : _root_.FiniteFreeComplex R e) :
    C.ExactInPositiveDegrees ↔
      ∀ i : Fin e,
        (LinearMap.exteriorRank (C.diffAt i) : ℤ) = C.alternatingRank i ∧
          (i.1 + 1 : WithTop ℕ) ≤ (I(C.diffAt i)).depth R := sorry

/-- Proposition 10.102.9: the source regular-sequence form of the Buchsbaum--Eisenbud criterion.
The depth formulation is `exactInPositiveDegrees_iff_rankMinorIdeal_depth`. -/
@[stacks 00N1 "Buchsbaum--Eisenbud criterion"]
theorem exactInPositiveDegrees_iff_buchsbaumEisenbud
    (C : _root_.FiniteFreeComplex R e) :
    C.ExactInPositiveDegrees ↔
      ∀ i : Fin e,
        (LinearMap.exteriorRank (C.diffAt i) : ℤ) = C.alternatingRank i ∧
          (I(C.diffAt i) = ⊤ ∨
            ∃ rs : List R, RingTheory.Sequence.IsRegular R rs ∧ Ideal.ofList rs ≤ I(C.diffAt i) ∧
              rs.length = i.1 + 1) := sorry

end FiniteFreeComplex
