/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Catenary.PrimeSpectrum
import StacksCheckRecall

@[expose] public section

/-!
# Catenary rings

@stack 00NI
-/

/- Definition 10.105.1: catenarity is owned by `IsCatenaryRing`; its
bounded-chain and equal-length prime-interval views are provided by
`ReasLib.RingTheory.Catenary.PrimeSpectrum`. -/
@[stacks 00NI "catenary ring"]
#check @IsCatenaryRing
@[stacks 00NI "bounded finite prime chains"]
#check @IsCatenaryRing.primeChainsBounded
@[stacks 00NI "equal lengths of maximal prime chains"]
#check @IsCatenaryRing.maximalPrimeChainsHaveSameLength
