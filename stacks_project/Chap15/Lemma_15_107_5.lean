/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalRing.Unibranch.StrictHenselization

/-!
@stack 06DM
-/

@[expose] public section

universe u v

/- Lemma 15.107.5, tag `06DM`: a local ring is geometrically unibranch exactly when a chosen
strict Henselization has a unique minimal prime. -/
@[stacks 06DM "Lemma 15.107.5"]
#check fun (A : Type u) (Ash : Type v) [CommRing A] [IsLocalRing A]
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash] ↦
  (IsGeometricallyUnibranch.StrictHenselization.iff_uniqueMinimalPrime
      (A := A) (Ash := Ash) :
    IsGeometricallyUnibranch A ↔ ∃! p : Ideal Ash, p ∈ minimalPrimes Ash)

#check @IsGeometricallyUnibranch.StrictHenselization.uniqueMinimalPrime
#check @IsGeometricallyUnibranch.StrictHenselization.of_uniqueMinimalPrime
