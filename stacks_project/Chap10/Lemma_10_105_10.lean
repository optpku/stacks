/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Catenary.DimensionFunction

/-!
# Lemma 10.105.10

The local-ring dimension-function characterization of catenarity lives in
`ReasLib.RingTheory.Catenary.DimensionFunction`.

@stack 0ECF
-/

@[stacks 0ECF "prime quotient dimension function"]
#check @PrimeSpectrum.quotientKrullDim

/- Lemma 10.105.10: a Noetherian local ring `A` is catenary if and only if the
function `p ↦ dim(A ⧸ p.asIdeal)` is a dimension function on `PrimeSpectrum A`. -/
@[stacks 0ECF]
#check @isCatenaryRing_iff_primeQuotientKrullDimension_isDimensionFunction
