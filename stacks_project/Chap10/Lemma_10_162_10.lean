/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.Normalization
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.Reduced
import StacksCheckRecall

@[expose] public section

/-!
# Analytically Unramified Local Rings

@stack 032Y

This source-facing file recalls the shared reducedness, minimal-prime, and
finite-normalization consequences of analytic unramifiedness.
-/

-- Lemma 10.162.10 (1), tag `032Y`: an analytically unramified Noetherian
-- local ring is reduced.
@[stacks 032Y "(1)"]
#check @IsAnalyticallyUnramified.isReduced

-- Lemma 10.162.10 (2), tag `032Y`: quotienting by a minimal prime preserves
-- analytic unramifiedness.
@[stacks 032Y "(2)"]
#check @IsAnalyticallyUnramified.minimalPrime

-- Lemma 10.162.10 (3), tag `032Y`: reducedness and analytic unramifiedness
-- of the minimal-prime quotients imply analytic unramifiedness.
@[stacks 032Y "(3)"]
#check @IsAnalyticallyUnramified.of_isReduced_of_minimalPrimes

-- Lemma 10.162.10 (4), tag `032Y`: the total-quotient normalization is
-- finite.
@[stacks 032Y "(4)"]
#check @IsAnalyticallyUnramified.integralClosure_fractionRing_finite

-- Lemma 10.162.10 (5), tag `032Y`: an analytically unramified Noetherian
-- local domain is `N-1`.
@[stacks 032Y "(5)"]
#check @IsAnalyticallyUnramified.isN1Ring
