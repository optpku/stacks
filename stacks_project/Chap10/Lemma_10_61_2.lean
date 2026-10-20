/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.Prime.FiniteSpectrum
import StacksCheckRecall

/-!
# Dimension of a Noetherian ring with finite spectrum

@stack 0ALV
-/

@[expose] public section

/- A Noetherian ring with finitely many prime ideals has the canonical Krull-dimension bound
`KrullDimLE 1`. -/
@[stacks 0ALV "canonical dimension bound"]
#check @Ring.krullDimLEOne_of_finitePrimeSpectrum

/- Lemma 10.61.2: a Noetherian ring with finitely many prime ideals has Krull dimension at most
`1`. -/
@[stacks 0ALV]
#check @Ring.krullDim_le_one_of_finitePrimeSpectrum
