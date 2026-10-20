/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Units and the Jacobson radical of an adic completion

@stack 05GI

This leaf owns the unit-detection API for the first quotient of an adic
completion and its Jacobson-radical consequences. No finite-generation
hypothesis on the ideal is needed.
-/

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Lemma 10.96.6 (1), tag `05GI`: an element of an adic completion is a
unit when its image in the first quotient is a unit. -/
@[stacks 05GI "unit detection in the first adic quotient"]
theorem isUnit_of_isUnit_evalOne (x : AdicCompletion I R)
    (hx : IsUnit (evalOneₐ I x)) :
    IsUnit x := sorry

/-- Lemma 10.96.6 (4), tag `05GI`: the kernel of the first quotient map is
contained in the Jacobson radical of the completion. -/
@[stacks 05GI "first-quotient kernel in the Jacobson radical"]
theorem ker_evalOne_le_jacobson :
    RingHom.ker (evalOneₐ I).toRingHom ≤
      Ideal.jacobson (⊥ : Ideal (AdicCompletion I R)) := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  apply isUnit_of_isUnit_evalOne I
  change evalOneₐ I x = 0 at hx
  simp [hx]

/-- Lemma 10.96.6 (4), tag `05GI`: the ideal extended to the completion is
contained in its Jacobson radical. -/
@[stacks 05GI "extended ideal in the Jacobson radical"]
theorem idealMap_le_jacobson :
    Ideal.map (algebraMap R (AdicCompletion I R)) I ≤
      Ideal.jacobson (⊥ : Ideal (AdicCompletion I R)) := by
  refine (Ideal.map_le_iff_le_comap).2 ?_
  intro x hx
  apply ker_evalOne_le_jacobson I
  change ((evalOneₐ I).toRingHom.comp
    (algebraMap R (AdicCompletion I R))) x = 0
  rw [evalOneₐ_comp_algebraMap_eq_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

/-- Lemma 10.96.6 (3), tag `05GI`: an element congruent to one modulo the
extended ideal is a unit in the completion. -/
@[stacks 05GI "unit congruent to one modulo the extended ideal"]
theorem isUnit_of_sub_one_mem_idealMap (x : AdicCompletion I R)
    (hx : x - 1 ∈ Ideal.map (algebraMap R (AdicCompletion I R)) I) :
    IsUnit x :=
  Ideal.isUnit_of_sub_one_mem_jacobson_bot x (idealMap_le_jacobson I hx)

/-- Lemma 10.96.6 (2), tag `05GI`: an element of the base ring congruent to
one modulo the ideal maps to a unit in the completion. -/
@[stacks 05GI "base element congruent to one maps to a unit"]
theorem isUnit_algebraMap_of_sub_one_mem (x : R) (hx : x - 1 ∈ I) :
    IsUnit (algebraMap R (AdicCompletion I R) x) := by
  apply isUnit_of_sub_one_mem_idealMap I
  simpa only [map_sub, map_one] using
    (Ideal.mem_map_of_mem (algebraMap R (AdicCompletion I R)) hx)

end AdicCompletion
