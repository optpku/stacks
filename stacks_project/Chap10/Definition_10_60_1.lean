/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.RelSeries
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.60.1

@stack 0GIE
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommRing R]

/- Domain sampling:
* Primary domain: order-theoretic strict chains in `Spec R`, viewed through the specialization
  order on `PrimeSpectrum R`.
* Owner declarations inspected in this domain:
  - `LTSeries`
  - `RelSeries.length`
  - `PrimeSpectrum.instPartialOrder`
  - `PrimeSpectrum.asIdeal_lt_asIdeal`
* Best owner abstraction: `LTSeries (PrimeSpectrum R)` is the canonical owner for finite strict
  chains of prime ideals; `RelSeries.length` is derived API on that owner.
* Primitive vs. derived: the chain itself is primitive data, while its length is the canonical
  derived field.
* Source/core/bridge triage: this file is source-facing, but it should remain a direct recall of
  the core/canonical owner abstraction rather than introducing any chapter-local wrapper.
-/

/- Definition 10.60.1: a chain of prime ideals of `R` is the canonical order-theoretic notion
`LTSeries (PrimeSpectrum R)`, i.e. a finite strictly increasing sequence
`𝔭₀ < 𝔭₁ < ⋯ < 𝔭ₙ` in `PrimeSpectrum R`. -/
@[stacks 0GIE "prime-ideal chains"]
#check (LTSeries (PrimeSpectrum R))

/- Companion recall: if `p : LTSeries (PrimeSpectrum R)` is a chain of prime ideals, then its
length is the canonical field `p.length`, i.e. `RelSeries.length p`. -/
@[stacks 0GIE "chain length"]
#check @RelSeries.length

end
