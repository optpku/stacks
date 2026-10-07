module

public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.DiscreteValuationRing.Characterization
public import ReasLib.RingTheory.Henselian.Henselization.KrullDimension
public import ReasLib.RingTheory.Henselian.Henselization.Regular
import Mathlib.Tactic.CrossRefAttribute

/-!
# Discrete valuation rings and henselization

The discrete valuation ring property is invariant under henselization and
strict henselization of a Noetherian local ring.

@stack 0AP3
-/

@[expose] public section

universe u v w

namespace IsHenselizationOf

variable {R : Type u} {Rh : Type v} {Rsh : Type w}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-- Lemma 15.45.11 (0AP3): the discrete valuation ring property of a
Noetherian local ring, a henselization, and a strict henselization are
equivalent. -/
@[stacks 0AP3 "DVR property under henselization"]
theorem isDiscreteValuationRing_tfae [IsNoetherianRing R] :
    List.TFAE
      [(∃ (_ : IsDomain R), IsDiscreteValuationRing R),
        (∃ (_ : IsDomain Rh), IsDiscreteValuationRing Rh),
        (∃ (_ : IsDomain Rsh), IsDiscreteValuationRing Rsh)] := sorry

end IsHenselizationOf
