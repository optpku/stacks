/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CompleteIntersection.RegularQuotient
import StacksCheckRecall

@[expose] public section

/- Lemma 23.8.2 (09Q0): the quotient of a prime localization of a regular ring by a regular
sequence contained in the prime is a complete-intersection local ring. -/
universe u

section

variable {R : Type u} [CommRing R] [IsRegularRing R]
variable (p : PrimeSpectrum R) (fs : List p.asIdeal)
variable (hfs : RingTheory.Sequence.IsRegular R (fs.map p.asIdeal.subtype))

@[stacks 09Q0]
#check (Ideal.AtPrime.RegularQuotient.isCompleteIntersection p fs hfs :
  IsCompleteIntersectionLocalRing
    ((Ideal.ofList (fs.map p.asIdeal.subtype)).quotientAtPrime p))

end

#check @Ideal.AtPrime.RegularQuotient.isGeneratedByRegularSequence
