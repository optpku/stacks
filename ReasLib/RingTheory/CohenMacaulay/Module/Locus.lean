/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Support
public import ReasLib.RingTheory.CohenMacaulay.Module

@[expose] public section

universe u v

namespace Module

variable (A : Type u) [CommRing A] [IsNoetherianRing A]
variable (M : Type v) [AddCommGroup M] [Module A M]

/-- The locus where the localization of `M` is zero or is Cohen-Macaulay over the
corresponding local ring. -/
def cohenMacaulayLocus : Set (PrimeSpectrum A) :=
  {p |
    Subsingleton (LocalizedModule.AtPrime p.asIdeal M) ∨
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)}

/-- Membership in the module Cohen-Macaulay locus is the disjunction of vanishing and
Cohen-Macaulayness after localization. -/
theorem mem_cohenMacaulayLocus (p : PrimeSpectrum A) :
    p ∈ cohenMacaulayLocus A M ↔
      Subsingleton (LocalizedModule.AtPrime p.asIdeal M) ∨
        Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M) := sorry

/-- Every prime outside the support of `M` lies in its module Cohen-Macaulay locus. -/
theorem mem_cohenMacaulayLocus_of_notMem_support
    {p : PrimeSpectrum A} (hp : p ∉ support A M) :
    p ∈ cohenMacaulayLocus A M := sorry

/-- On the support of `M`, membership in its module Cohen-Macaulay locus is precisely
Cohen-Macaulayness after localization. -/
theorem mem_cohenMacaulayLocus_iff_of_mem_support
    {p : PrimeSpectrum A} (hp : p ∈ support A M) :
    p ∈ cohenMacaulayLocus A M ↔
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M) := sorry

end Module
