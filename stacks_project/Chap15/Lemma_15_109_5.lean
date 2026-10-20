/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Branches.DimensionOne
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.109.5 (0C2B)

@stack 0C2B
-/

open IsLocalRing

universe u v

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

-- Lemma 15.109.5, one-dimensional completion branches come from henselization branches.
@[stacks 0C2B "Lemma 15.109.5"]
#check fun
    (iota : IsHenselizationOf.Completion.Comparison (R := A) (Rh := Ah))
    (q : minimalPrimes (AdicCompletion (maximalIdeal A) A))
    (hdim : ringKrullDim (AdicCompletion (maximalIdeal A) A ⧸ q.1) = 1) ↦
  (IsHenselizationOf.Completion.Comparison.exists_minimalPrime_of_completion_quotient_dimension_one
      iota q hdim :
    ∃ qh : minimalPrimes Ah,
      (q : Ideal (AdicCompletion (maximalIdeal A) A)) =
        Ideal.radical (Ideal.map iota.toAlgHom.toRingHom qh))
