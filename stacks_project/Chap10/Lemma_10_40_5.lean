/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Module
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.40.5

@stack 00L2
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Lemma 10.40.5, canonical main form: more precisely, if
`I = Module.annihilator R M`, then `PrimeSpectrum.zeroLocus I = Module.support R M`. -/
@[stacks 00L2 "support as a zero locus"]
#check @Module.support_eq_zeroLocus

/- Source-wording consequence: if `M` is finite, then `Module.support R M` is closed. -/
@[stacks 00L2 "closedness of finite support"]
#check @Module.isClosed_support

end
