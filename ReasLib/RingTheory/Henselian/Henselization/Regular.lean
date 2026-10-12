/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.Henselian.FaithfullyFlat
public import ReasLib.RingTheory.Henselian.Noetherian
public import ReasLib.RingTheory.RegularLocalRing.Fiber
public import ReasLib.RingTheory.RegularLocalRing.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular local rings and henselization

Regularity of a Noetherian local ring is invariant under henselization and
strict henselization.

@stack 06LN
-/

@[expose] public section

universe u v w

namespace IsHenselizationOf

variable {R : Type u} {Rh : Type v} {Rsh : Type w}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-- Lemma 15.45.10 (06LN): regularity of a Noetherian local ring, a
henselization, and a strict henselization are equivalent. -/
@[stacks 06LN "regularity under henselization"]
theorem isRegularLocalRing_tfae [IsNoetherianRing R] :
    List.TFAE [IsRegularLocalRing R, IsRegularLocalRing Rh,
      IsRegularLocalRing Rsh] := sorry

end IsHenselizationOf

namespace IsHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- A Noetherian local ring is regular if and only if a henselization is
regular. -/
@[stacks 06LN "regularity under henselization"]
theorem isRegularLocalRing_iff [IsNoetherianRing R] :
    IsRegularLocalRing R ↔ IsRegularLocalRing S := sorry

end IsHenselizationOf

namespace IsStrictHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [Algebra R S] [IsStrictHenselizationOf R S]

/-- A Noetherian local ring is regular if and only if a strict
henselization is regular. -/
@[stacks 06LN "regularity under strict henselization"]
theorem isRegularLocalRing_iff [IsNoetherianRing R] :
    IsRegularLocalRing R ↔ IsRegularLocalRing S := sorry

end IsStrictHenselizationOf
