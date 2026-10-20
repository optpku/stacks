/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.LocallyFree.Finite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular principal products of ideals

This leaf owns the symmetric rank-one consequence of a regular principal product of ideals.
The pair-valued theorem is the primary interface; the left/right finite-generation and rank-one
projections are thin convenience views for downstream arguments.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-- A regular principal product makes both factors finite locally free of rank one. -/
@[stacks 09ME "rank-one pair"]
theorem finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular
    (I J : Ideal R) (f : R) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set R)) :
    Module.FiniteLocallyFreeOfRank R I 1 ∧ Module.FiniteLocallyFreeOfRank R J 1 := sorry

/-- If ideals `I` and `J` have regular principal product `(f)`, then `I` is finitely generated. -/
@[stacks 09ME "(1)"]
theorem left_fg_of_mul_eq_span_singleton_regular
    (I J : Ideal R) (f : R) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set R)) : I.FG := sorry

/-- If ideals `I` and `J` have regular principal product `(f)`, then `I` is finite locally free
of rank one. -/
@[stacks 09ME "(2)"]
theorem left_finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular
    (I J : Ideal R) (f : R) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set R)) :
    Module.FiniteLocallyFreeOfRank R I 1 := sorry

/-- If ideals `I` and `J` have regular principal product `(f)`, then `J` is finitely generated. -/
@[stacks 09ME "(3)"]
theorem right_fg_of_mul_eq_span_singleton_regular
    (I J : Ideal R) (f : R) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set R)) : J.FG := sorry

/-- If ideals `I` and `J` have regular principal product `(f)`, then `J` is finite locally free
of rank one. -/
@[stacks 09ME "(4)"]
theorem right_finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular
    (I J : Ideal R) (f : R) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set R)) :
    Module.FiniteLocallyFreeOfRank R J 1 := sorry

end Ideal
