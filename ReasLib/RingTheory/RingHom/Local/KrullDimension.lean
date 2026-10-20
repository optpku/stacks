/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.Fiber
public import ReasLib.RingTheory.RingHom.Local.Surjective

@[expose] public section

/-!
# Krull Dimension of a Localized Surjective Presentation

This leaf compares the local source ring of a surjective ring homomorphism
with its quotient by the localized kernel.  It is phrased using the intrinsic
prime height defect rather than a chosen polynomial presentation.
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.135.4, tag `00SC`: for a surjective ring homomorphism, the Krull dimension of the
quotient of the local source ring by the localized kernel differs from that of the local source
ring by the prime height defect. -/
@[stacks 00SC "local quotient dimension from prime height defect"]
theorem localQuotientAt_ringKrullDim_add_eq
    (f : R →+* S) (hf : Function.Surjective f) (q : PrimeSpectrum S)
    {c : ℕ} (hc : f.primeHeightDefect q = c) :
    ringKrullDim (f.localQuotientAt q) + c = ringKrullDim (f.sourceLocalRingAt q) := sorry

end RingHom
