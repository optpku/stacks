/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.CoprimeToSix
import StacksCheckRecall

@[expose] public section

/- Exercise 111.7.3 (1): The localization of ℤ at integers coprime to 6 is a domain. -/
@[stacks 0769]
#check (Localization.CoprimeToSix.instIsDomain : IsDomain Localization.CoprimeToSix.Integers)

/- Exercise 111.7.3 (2): The chosen domain has three pairwise distinct prime ideals. -/
@[stacks 0769]
#check (Localization.CoprimeToSix.hasThreePairwiseDistinctPrimes :
  Function.Injective Localization.CoprimeToSix.primes ∧
    ∀ index, (Localization.CoprimeToSix.primes index).IsPrime)

/- Exercise 111.7.3 (3): The principal localization away from the image of 6 is a field. -/
@[stacks 0769]
#check (Localization.CoprimeToSix.isField_away_six :
  IsField (Localization.Away Localization.CoprimeToSix.six))
