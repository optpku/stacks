/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Irreducible
public import ReasLib.RingTheory.Spectrum.Prime.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Prime-spectrum irreducibility support

The reusable ring-level criteria now live under `PrimeSpectrum`; this chapter file is retained as
a compatibility recall for the old support path and introduces no second implementation.

@stack 00I7
@stack 0G31
-/

/- Unique minimal-prime criterion. -/
@[stacks 00I7]
#check @PrimeSpectrum.irreducible_iff_unique_minimalPrime

/- Injective descent. -/
@[stacks 0G31]
#check @PrimeSpectrum.irreducible_of_injective

/- Localization stability. -/
@[stacks 0G31]
#check @PrimeSpectrum.irreducible_of_isLocalization

end
