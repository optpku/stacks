/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.CohenMacaulay.Locus

@[expose] public section

/-!
# Cohen--Macaulay locus recall

The reusable owner is `PrimeSpectrum.cohenMacaulayLocus`, whose pointwise API
uses the local self-module formulation of Cohen--Macaulayness.  This preserves
the source statement without imposing a global `CohenMacaulayRing` assumption.

@stack 00RF
-/

/- Lemma 10.130.2, tag 00RF: for a finite-type algebra `S` over a field `k`, the primes `q`
such that `Localization.AtPrime q.asIdeal` is Cohen--Macaulay form an open subset of `Spec(S)`. -/
@[stacks 00RF "openness of the Cohen-Macaulay locus"]
#check @PrimeSpectrum.isOpen_cohenMacaulayLocus_of_finiteType
