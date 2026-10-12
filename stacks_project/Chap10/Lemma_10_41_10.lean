/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.41.10

@stack 037G
-/

@[stacks 037G "tensor-product projection is open on spectra"]
#check @PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field
