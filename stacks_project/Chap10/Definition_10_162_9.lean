/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified
import StacksCheckRecall

@[expose] public section

/-!
# Analytically Unramified Local Rings

@stack 032X

This chapter item is a source-facing recall of the shared adic-completion
definition.
-/

-- Definition 10.162.9, tag `032X`: a local ring is analytically unramified
-- when its maximal-ideal adic completion is reduced.
@[stacks 032X]
#check @IsAnalyticallyUnramified
@[stacks 032X "prime-spectrum formulation"]
#check @PrimeSpectrum.IsAnalyticallyUnramified
