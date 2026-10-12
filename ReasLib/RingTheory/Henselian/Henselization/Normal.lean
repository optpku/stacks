/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.Henselian.FaithfullyFlat
public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Normal
public import ReasLib.RingTheory.RingHom.IndEtale.Normal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Normality and henselization

Normality is invariant under henselization and strict henselization of a local
ring.

@stack 06DI
-/

@[expose] public section

universe u v w

namespace IsHenselizationOf

variable {R : Type u} {Rh : Type v} {Rsh : Type w}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-- Lemma 15.45.6 (06DI): normality of a local ring, a henselization,
and a strict henselization are equivalent. -/
@[stacks 06DI "normality under henselization and strict henselization"]
theorem isNormalRing_tfae :
    List.TFAE [IsNormalRing R, IsNormalRing Rh, IsNormalRing Rsh] := sorry

end IsHenselizationOf

namespace IsHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- A local ring is normal if and only if a henselization is normal. -/
@[stacks 06DI "normality under henselization"]
theorem isNormalRing_iff : IsNormalRing R ↔ IsNormalRing S := sorry

end IsHenselizationOf

namespace IsStrictHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [Algebra R S] [IsStrictHenselizationOf R S]

/-- A local ring is normal if and only if a strict henselization is normal. -/
@[stacks 06DI "normality under strict henselization"]
theorem isNormalRing_iff : IsNormalRing R ↔ IsNormalRing S := sorry

end IsStrictHenselizationOf
