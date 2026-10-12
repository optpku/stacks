/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import ReasLib.RingTheory.Completion.LocalRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Krasner's lemma for complete local domains

A simple root over a one-dimensional complete local domain persists under sufficiently small
coefficient perturbations.

@stack 09EI
-/

@[expose] public section

open IsLocalRing Polynomial

universe u

namespace IsCompleteLocalRing

/-- Lemma 15.114.1 (Krasner's lemma), Stacks `09EI` (current Stacks Lemma 15.115.1): over a
one-dimensional complete local domain, a simple root persists under sufficiently small
coefficient perturbations, with the new root congruent to the original root to any prescribed
maximal-adic precision. -/
@[stacks 09EI "Krasner's lemma for a complete local domain"]
theorem existsRoot_of_smallPerturbation
    {A : Type u} [CommRing A] [IsDomain A] [IsCompleteLocalRing A]
    (hdim : ringKrullDim A = 1) (P : A[X]) {alpha : A} (hroot : P.IsRoot alpha)
    (hderivative : P.derivative.eval alpha ≠ 0) (c : ℕ) :
    ∃ n : ℕ, ∀ Q : A[X], Q ∈ (maximalIdeal A ^ n).map C →
      ∃ beta : A, (P + Q).IsRoot beta ∧ beta ≡ alpha [SMOD maximalIdeal A ^ c] := sorry
-- Proof strategy: separate the field case, where `maximalIdeal A = ⊥` forces every admissible
-- perturbation to vanish, from the nonfield case.  In the latter, use `hdim` and
-- `Ring.krullDimLE_one_iff_of_noZeroDivisors` to show that every nonzero principal ideal contains
-- a power of `maximalIdeal A`.  Clear the denominator of `P.derivative.eval alpha` in
-- `FractionRing A`, translate at `alpha`, and scale by a nonzero maximal-ideal element.  The
-- coefficientwise characterization `Ideal.mem_map_C_iff` then makes both the value and derivative
-- errors sufficiently small for the henselian lifting supplied by completeness.  Undoing the
-- translation and scaling gives the required root and the stated `SModEq` congruence.

end IsCompleteLocalRing
