/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.Dimension
public import ReasLib.RingTheory.CohenMacaulay.Module.Local
public import ReasLib.RingTheory.CohenMacaulay.Module.PrimeChain
public import ReasLib.RingTheory.Module.Support.Self
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohen-Macaulay self-modules

@stack 00N9
@stack 00NA
@stack 00NB

These are the ring-facing specializations of the corresponding module theorems. Keeping them in
one leaf avoids rebuilding the `Module.CohenMacaulay R R` instance and the full-support bridge at
each source use site.
-/

@[expose] public section

universe u

namespace Module.CohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [Module.CohenMacaulay R R]

/-- Lemma 10.104.3: every maximal prime chain in a Noetherian local Cohen-Macaulay ring has
length equal to the Krull dimension of the ring. -/
@[stacks 00N9]
theorem length_eq_ringKrullDim_of_maximal_chain_self
    (p : LTSeries (PrimeSpectrum R)) (hp : IsMaxChain (· ≤ ·) (Set.range p)) :
    p.length = ringKrullDim R := sorry

/-- Lemma 10.104.4: the dimension of a Noetherian local Cohen-Macaulay ring is the sum of the
dimensions of its localization and quotient at any prime. -/
@[stacks 00NA]
theorem ringKrullDim_eq_localizationAtPrime_add_quotient_self
    (p : Ideal R) [p.IsPrime] :
    ringKrullDim R = ringKrullDim (Localization.AtPrime p) + ringKrullDim (R ⧸ p) := sorry

/-- Lemma 10.104.5: localization at a prime preserves Cohen-Macaulayness of a Noetherian local
ring viewed as its self-module. -/
@[stacks 00NB]
theorem localizationAtPrime_self (p : Ideal R) [p.IsPrime] :
    Module.CohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) := sorry

end Module.CohenMacaulay
