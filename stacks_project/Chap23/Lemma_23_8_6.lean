/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CompleteIntersection.Localization
import StacksCheckRecall

@[expose] public section

/- Lemma 23.8.6 (09Q4): a complete-intersection local ring remains a complete intersection after
localization at any prime ideal. -/
universe u

section

variable {A : Type u} [CommRing A] [IsCompleteIntersectionLocalRing A]
variable (p : PrimeSpectrum A)

@[stacks 09Q4]
#check (IsCompleteIntersectionLocalRing.localizationAtPrime p :
  IsCompleteIntersectionLocalRing (Localization.AtPrime p.asIdeal))

end
