/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.CompactOpen
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.29.1 (Tag 00F6): compact-open descriptions in a prime spectrum.

@stack 00F6
-/

/- Lemma 10.29.1, tag 00F6: the four standard descriptions of a retrocompact
open subset of a prime spectrum. -/
@[stacks 00F6]
#check @PrimeSpectrum.retrocompact_open_tfae

@[stacks 00F6 "retrocompact-open owner"]
#check @QuasiSeparatedSpace.isRetrocompact_iff_isCompact

@[stacks 00F6 "finite basic-open presentation"]
#check @PrimeSpectrum.isCompact_isOpen_iff

@[stacks 00F6 "finitely generated ideal presentation"]
#check @PrimeSpectrum.isCompact_isOpen_iff_ideal
