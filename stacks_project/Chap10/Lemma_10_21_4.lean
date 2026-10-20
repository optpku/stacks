/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Connected
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.21.4

@stack 00EF
-/

/- Lemma 10.21.4 (Tag 00EF): for a nonzero commutative ring, connectedness of
the prime spectrum is equivalent to triviality of all idempotents. -/
@[stacks 00EF]
#check @PrimeSpectrum.connectedSpace_iff_idempotents_trivial
