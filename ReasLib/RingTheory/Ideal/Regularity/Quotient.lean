/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.Regularity
import Mathlib.Tactic.CrossRefAttribute

/-!
# H1-regular quotient ideals

An H1-regular quotient ideal controls the intersection of the lower ideal with
the square of the upper ideal.

@stack 07CX
-/

@[expose] public section

universe u

namespace Ideal.IsH1RegularIdeal

variable {A : Type u} [CommRing A]

/-- Lemma 15.32.5 (Stacks tag `07CX`): if `J / I` is an
H1-regular ideal of `A / I`, then `I ⊓ J ^ 2 = I * J`. -/
@[stacks 07CX "Lemma 15.32.5"]
theorem inf_sq_eq_mul {I J : Ideal A}
    (hreg : (J.map (Ideal.Quotient.mk I)).IsH1RegularIdeal) (hIJ : I ≤ J) :
    I ⊓ J ^ 2 = I * J := sorry

end Ideal.IsH1RegularIdeal
