/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Connected.Idempotent
import StacksCheckRecall

/-!
# Closed unions of connected components

@stack 04PP
-/

@[expose] public section

@[stacks 04PP "source three-clause form"]
#check @PrimeSpectrum.IdempotentIdeal.tfae

@[stacks 04PP "idempotent-generated zero-locus presentation"]
#check @PrimeSpectrum.IdempotentIdeal.exists_zeroLocus_eq

@[stacks 04PP "uniqueness of the idempotent-generated ideal"]
#check @PrimeSpectrum.IdempotentIdeal.existsUnique_zeroLocus_eq

@[stacks 04PP "clopen-intersection criterion"]
#check @Set.isIntersectionOfClopens_iff

@[stacks 04PP "idempotent-generated ideals are pure"]
#check @Ideal.IsGeneratedByIdempotents.pure

@[stacks 04PP "pure-ideal zero-locus uniqueness"]
#check @Ideal.zeroLocus_inj_of_pure
