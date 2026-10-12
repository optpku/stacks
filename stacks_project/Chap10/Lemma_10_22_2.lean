/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Connected.Idempotent
import StacksCheckRecall

/-!
# Lemma 10.22.2

@stack 00EG
-/

@[expose] public section

@[stacks 00EG "connected component as an idempotent-generated zero locus"]
#check @PrimeSpectrum.exists_isGeneratedByIdempotents_connectedComponent_eq_zeroLocus

@[stacks 00EG "idempotents in a connected-component quotient"]
#check @PrimeSpectrum.idempotent_quotient_eq_zero_or_one_of_connectedComponent_eq_zeroLocus

@[stacks 00EG "idempotent-generated ideal predicate"]
#check @Ideal.IsGeneratedByIdempotents
