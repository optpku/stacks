/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.PrimeLocalization
import StacksCheckRecall

/-!
# Remark 15.25.5

@stack 05GS

The detection condition and its five source criteria are owned by the prime-localization API.
-/

@[expose] public section

/- The condition that a finite family of prime localizations detects equality. -/
#check @PrimeLocalization.DetectsEquality

/- Remark 15.25.5 (1): local rings satisfy the detection condition. -/
@[stacks 05GS "Remark 15.25.5 (1)"]
#check @PrimeLocalization.DetectsEquality.ofIsLocalRing

/- Remark 15.25.5 (2): Noetherian rings satisfy the detection condition. -/
@[stacks 05GS "Remark 15.25.5 (2)"]
#check @PrimeLocalization.DetectsEquality.ofIsNoetherianRing

/- Remark 15.25.5 (3): domains satisfy the detection condition. -/
@[stacks 05GS "Remark 15.25.5 (3)"]
#check @PrimeLocalization.DetectsEquality.ofIsDomain

/- Remark 15.25.5 (4): reduced rings with finitely many minimal primes satisfy the detection
condition. -/
@[stacks 05GS "Remark 15.25.5 (4)"]
#check @PrimeLocalization.DetectsEquality.ofIsReducedOfFiniteMinimalPrimes

/- Remark 15.25.5 (5): rings with finitely many weakly associated primes satisfy the detection
condition. -/
@[stacks 05GS "Remark 15.25.5 (5)"]
#check @PrimeLocalization.DetectsEquality.ofFiniteWeaklyAssociatedPrimes
