/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

/-!
# Prime-Spectrum Functoriality Recall

Continuity and the basic-open pullback formula are owned by `PrimeSpectrum`.

@stack 00E2
-/

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Lemma 10.17.4: for a ring homomorphism `φ : R →+* S`, the induced map
`PrimeSpectrum.comap φ : Spec(S) → Spec(R)` is continuous; this is the canonical theorem
`PrimeSpectrum.continuous_comap`. -/
@[stacks 00E2 "(1) continuity of the induced map on prime spectra"]
#check @PrimeSpectrum.continuous_comap

/- Lemma 10.17.4: the inverse image of a basic open `D(f)` under the induced map on spectra is
`D(φ(f))`; this is the canonical basic-open pullback theorem
`PrimeSpectrum.comap_basicOpen`. -/
@[stacks 00E2 "(2) pullback of a basic open"]
#check @PrimeSpectrum.comap_basicOpen

end
