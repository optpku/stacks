/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalRing.Unibranch.Henselization

/-!
@stack 0BQ0
-/

@[expose] public section

universe u v

/- Lemma 15.107.3, tag `0BQ0`: a local ring is unibranch exactly when a chosen Henselization has
a unique minimal prime. -/
@[stacks 0BQ0 "Lemma 15.107.3"]
#check fun (A : Type u) (Ah : Type v) [CommRing A] [IsLocalRing A]
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah] ↦
  (IsUnibranch.Henselization.iff_uniqueMinimalPrime (A := A) (Ah := Ah) :
    IsUnibranch A ↔ ∃! p : Ideal Ah, p ∈ minimalPrimes Ah)

#check @IsUnibranch.Henselization.uniqueMinimalPrime
#check @IsUnibranch.Henselization.of_uniqueMinimalPrime
#check @IsUnibranch.uniqueMinimalPrime
