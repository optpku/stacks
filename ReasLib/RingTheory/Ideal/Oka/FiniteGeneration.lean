/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Noetherian.OfPrime
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finitely generated ideals as an Oka family

@stack 05KB

The explicit generator calculation is kept alongside Mathlib's canonical Oka-family theorem so
that arguments needing actual finite generating sets do not have to unpack the Oka proof.
-/

universe u

namespace Ideal

/-- Example 10.28.4: generators of a colon ideal and of `I ⊔ (a)` combine to generate `I`. -/
@[stacks 05KB "explicit generator calculation"]
theorem eq_span_mul_image_union_of_colon_sup_eq
    {R : Type u} [CommRing R] {I : Ideal R} {a : R} {s t : Finset R}
    (hcolon : I.colon (span ({a} : Set R)) = span (s : Set R))
    (hsup : I ⊔ span ({a} : Set R) = span (insert a (t : Set R)))
    (ht : (t : Set R) ⊆ (I : Set R)) :
    I = span (((a * ·) '' (s : Set R)) ∪ (t : Set R)) := sorry

end Ideal
