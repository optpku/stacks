/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.Henselian.FaithfullyFlat
public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Reduced
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reducedness and henselization

Reducedness is invariant under henselization and strict henselization of a
local ring.

@stack 06DH
-/

@[expose] public section

universe u v w

namespace IsHenselizationOf

variable {R : Type u} {Rh : Type v} {Rsh : Type w}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-- Reducedness of a local ring, its henselization, and its strict henselization
are equivalent. -/
@[stacks 06DH "reducedness under henselization and strict henselization"]
theorem isReduced_tfae :
    List.TFAE [IsReduced R, IsReduced Rh, IsReduced Rsh] := sorry

end IsHenselizationOf

namespace IsHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- A local ring is reduced if and only if a henselization is reduced. -/
@[stacks 06DH "reducedness under henselization"]
theorem isReduced_iff : IsReduced R ↔ IsReduced S := sorry

end IsHenselizationOf

namespace IsStrictHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [Algebra R S] [IsStrictHenselizationOf R S]

/-- A local ring is reduced if and only if a strict henselization is
reduced. -/
@[stacks 06DH "reducedness under strict henselization"]
theorem isReduced_iff : IsReduced R ↔ IsReduced S := sorry

end IsStrictHenselizationOf
