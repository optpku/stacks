/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Pullback.Spectrum
import StacksCheckRecall

/-!
# Lemma 15.6.2

@stack 0B7J

In Situation 15.6.1, the spectrum of the fibre-product ring is the topological pushout of the
other three spectra.  The shared owner keeps all four `PrimeSpectrum.comap` maps explicit.
-/

@[stacks 0B7J "spectrum of the pullback ring"]
#check @SurjectiveRingPullbackSituation.specBprime

@[stacks 0B7J "spectrum map from the common target to B"]
#check @SurjectiveRingPullbackSituation.specToB

@[stacks 0B7J "spectrum map from the common target to A-prime"]
#check @SurjectiveRingPullbackSituation.specToAprime

@[stacks 0B7J "spectrum map from B to the pullback"]
#check @SurjectiveRingPullbackSituation.specBToBprime

@[stacks 0B7J "spectrum map from A-prime to the pullback"]
#check @SurjectiveRingPullbackSituation.specAprimeToBprime

@[stacks 0B7J "spectrum square commutes"]
#check @SurjectiveRingPullbackSituation.specSquare_commutes

@[stacks 0B7J "Lemma 15.6.2 spectrum pushout"]
#check @SurjectiveRingPullbackSituation.spec_isPushout
