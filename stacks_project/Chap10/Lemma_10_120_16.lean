/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.RegularProduct
import StacksCheckRecall

/-!
# Ideal factors of a regular principal product

@stack 09ME
-/

@[expose] public section

universe u

namespace Ideal

variable {A : Type u} [CommRing A]

/- Lemma 10.120.16 (Stacks `09ME`): the four source clauses are views of the symmetric reusable
regular-principal-product owner in `ReasLib.RingTheory.Ideal.RegularProduct`. -/
@[stacks 09ME "(1)"]
#check @Ideal.left_fg_of_mul_eq_span_singleton_regular
@[stacks 09ME "(2)"]
#check @Ideal.left_finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular
@[stacks 09ME "(3)"]
#check @Ideal.right_fg_of_mul_eq_span_singleton_regular
@[stacks 09ME "(4)"]
#check @Ideal.right_finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular

@[stacks 09ME "symmetric finite-locally-free package"]
#check (Ideal.finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular (R := A))

end Ideal
