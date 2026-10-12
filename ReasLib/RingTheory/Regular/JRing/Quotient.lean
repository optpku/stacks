/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.Quotient.PrimeSpectrum
public import ReasLib.RingTheory.Regular.JRing
public import ReasLib.RingTheory.Spectrum.Prime.Neighborhood
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Quotient criteria for J-rings

@stack 07P8
@stack 07P9

The regular-locus trace criterion is kept separate from its prime-quotient
consequence so that downstream arguments can use either level directly.
-/

universe u

open PrimeSpectrum
open scoped PrimeSpectrum

namespace IsJ1Ring

/-- A Noetherian ring is `J-1` exactly when every regular point has a nonempty ambient-open trace
on its closure that consists of regular points. This is Lemma 15.47.2. -/
@[stacks 07P8 "regular-point trace criterion for J-1 rings"]
theorem iff_regularPoint_zeroLocus
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsJ1Ring R ↔
      ∀ p ∈ Reg(Spec R),
        ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ (U ∩ zeroLocus p.asIdeal).Nonempty ∧
          U ∩ zeroLocus p.asIdeal ⊆ Reg(Spec R) := sorry

/-- If every prime quotient of a Noetherian ring is `J-0`, then the ring is `J-1`. This is
Lemma 15.47.3. -/
@[stacks 07P9 "J-1 from J-0 prime quotients"]
theorem of_primeQuotient_isJ0
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (h_quotient : ∀ p : PrimeSpectrum R, IsJ0Ring (R ⧸ p.asIdeal)) :
    IsJ1Ring R := sorry

end IsJ1Ring
