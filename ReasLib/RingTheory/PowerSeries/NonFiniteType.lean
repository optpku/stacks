/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

universe u

namespace PowerSeries

/-- The formal power series ring over a field is not a finite-type algebra over that field. -/
theorem not_finiteType (k : Type u) [Field k] : ¬ Algebra.FiniteType k (PowerSeries k) :=
  sorry

/-- The formal variable is not nilpotent in a formal power series ring over a field. -/
theorem not_isNilpotent_X (k : Type u) [Field k] : ¬ IsNilpotent (X : PowerSeries k) :=
  sorry

/-- Every maximal ideal of a formal power series ring over a field contains the formal variable. -/
theorem not_exists_isMaximal_notMem_X (k : Type u) [Field k] :
    ¬ ∃ m : Ideal (PowerSeries k), m.IsMaximal ∧ X ∉ m :=
  sorry

end PowerSeries
