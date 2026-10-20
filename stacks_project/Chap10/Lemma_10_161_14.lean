/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.Locus
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.161.14
@stack 0332

The normal locus is a reusable prime-spectrum object, so its owner and its
openness criteria live in `ReasLib.RingTheory.Normal.Locus`.
-/

/- Lemma 10.161.14, tag `0332`: if `R` is a Noetherian domain and some
nonzero localization `R_f` is normal, then the normal locus is open in
`PrimeSpectrum R`. -/
@[stacks 0332]
#check @PrimeSpectrum.normalLocus
#check @PrimeSpectrum.mem_normalLocus
#check @PrimeSpectrum.mem_normalLocus_iff_isIntegrallyClosed
#check @PrimeSpectrum.NormalLocus.isOpen_of_exists_normal_localizationAway
#check @PrimeSpectrum.NormalLocus.isOpen_of_exists_integrallyClosed_localizationAway
