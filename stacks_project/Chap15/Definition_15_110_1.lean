/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Catenary.Formal

@[expose] public section

/-!
# Definition 15.110.1

@stack 0AW2
-/

open IsLocalRing

universe u

/- Definition 15.110.1 (current Stacks numbering: Definition 15.111.1, tag
`0AW2`): a Noetherian local ring is formally catenary when every minimal-prime
quotient of its maximal-ideal completion has equidimensional spectrum. -/
@[stacks 0AW2 "Definition 15.110.1"]
#check fun (A : Type u) [CommRing A] ↦ (IsFormallyCatenaryRing A : Prop)

section

variable (A : Type u) [CommRing A] [IsFormallyCatenaryRing A]

#check fun (p : minimalPrimes A) ↦
  (IsFormallyCatenaryRing.equidimensional_completion_quotient (A := A) p :
    TopologicalSpace.EquidimensionalSpace
      (PrimeSpectrum
        (AdicCompletion (maximalIdeal A) A ⧸
          Ideal.map (algebraMap A (AdicCompletion (maximalIdeal A) A)) p.1)))

end

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

#check (IsFormallyCatenaryRing.iff A :
  IsFormallyCatenaryRing A ↔
    ∀ p : minimalPrimes A,
      TopologicalSpace.EquidimensionalSpace
        (PrimeSpectrum
          (AdicCompletion (maximalIdeal A) A ⧸
            Ideal.map (algebraMap A (AdicCompletion (maximalIdeal A) A)) p.1)))

end
