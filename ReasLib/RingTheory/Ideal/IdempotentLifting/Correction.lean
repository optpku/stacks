/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Group.Idempotent

/-!
# Polynomial Corrections of Nearly Idempotent Elements

This leaf owns the ring-level correction of an element whose idempotency defect is
nilpotent.  It is independent of the commutative ideal predicates in the parent
module, so noncommutative downstream users can import this leaf directly.
-/

@[expose] public section

universe u

open scoped Polynomial

namespace IsNilpotent

variable {A : Type u} [Ring A]

/-- A nilpotent idempotency defect admits an idempotent correction by a right multiple of that
defect.  This witness-agnostic form is convenient when only the corrected idempotent is needed. -/
@[stacks 05BU "idempotent correction by a nilpotent defect"]
theorem exists_idempotent_correction {e : A} (he : IsNilpotent (e ^ 2 - e)) :
    ∃ c : A, IsIdempotentElem (e + (e ^ 2 - e) * c) := sorry

/-- Lemma 10.32.7 (Tag 05BU): if `e ^ 2 - e` is nilpotent, then an idempotent correction has the
form `e + (e ^ 2 - e) * Polynomial.aeval e q` for an integer polynomial `q`.  The source's
finite sum in `e` and `e ^ 2 - e` has this form because `e ^ 2 - e` is itself an integer
polynomial evaluated at `e`. -/
@[stacks 05BU "polynomial correction of a nilpotent idempotency defect"]
theorem exists_polynomial_idempotent_correction {e : A} (he : IsNilpotent (e ^ 2 - e)) :
    ∃ q : ℤ[X], IsIdempotentElem (e + (e ^ 2 - e) * Polynomial.aeval e q) := sorry

end IsNilpotent
