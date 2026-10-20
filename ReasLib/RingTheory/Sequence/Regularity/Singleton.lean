/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Empty and singleton regular sequences

@stack 032C
-/

@[expose] public section

open IsLocalRing

universe u v

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The empty list is a regular sequence exactly when the module is nontrivial. -/
@[simp, stacks 032C "regularity of the empty sequence"]
theorem isRegular_nil_iff : IsRegular M ([] : List R) ↔ Nontrivial M := by
  constructor
  · intro h
    have hne : (⊤ : Submodule R M) ≠ ⊥ := by
      simpa using h.top_ne_smul
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    exact hne (Subsingleton.elim _ _)
  · intro h
    -- `IsRegular` consumes nontriviality as a class; this branch supplies the explicit iff input.
    letI : Nontrivial M := h
    rw [isRegular_iff]
    constructor
    · rw [isWeaklyRegular_iff_Fin]
      simp
    · simp

/-- A singleton is regular exactly when its entry acts regularly and the quotient is
nontrivial. -/
@[simp, stacks 032C "regularity of a singleton sequence"]
theorem isRegular_singleton_iff (x : R) :
    IsRegular M [x] ↔ IsSMulRegular M x ∧ Nontrivial (QuotSMulTop x M) := by
  rw [isRegular_cons_iff, isRegular_nil_iff (R := R)]

/-- Over a local ring, a finite nontrivial module and an element of the maximal ideal form a
regular singleton exactly when the element acts regularly. -/
@[stacks 032C "regular singleton in the maximal ideal"]
theorem isRegular_singleton_iff_of_mem_maximalIdeal
    [IsLocalRing R] [Module.Finite R M] [Nontrivial M]
    {x : R} (hx : x ∈ maximalIdeal R) :
    IsRegular M [x] ↔ IsSMulRegular M x := by
  constructor
  · intro h
    exact (isWeaklyRegular_singleton_iff M x).mp h.toIsWeaklyRegular
  · intro hreg
    exact IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M
      (by
        intro r hr
        simpa [List.mem_singleton.mp hr] using hx)
      ((isWeaklyRegular_singleton_iff M x).2 hreg)

end RingTheory.Sequence
