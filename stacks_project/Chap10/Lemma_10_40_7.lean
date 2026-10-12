/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Support.Cyclic
import StacksCheckRecall

/-!
# Lemma 10.40.7

@stack 07Z5
-/

@[expose] public section

@[stacks 07Z5 "support formulation"]
#check @Module.mem_support_span_singleton_iff_mkLinearMap_ne_zero

@[stacks 07Z5 "zero-locus formulation"]
#check @PrimeSpectrum.mem_zeroLocus_torsionOf_iff_mkLinearMap_ne_zero

@[stacks 07Z5 "localized element criterion"]
#check @LocalizedModule.mkLinearMap_apply_ne_zero_iff_torsionOf_le
