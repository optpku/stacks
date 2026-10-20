/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.FilteredColimit
public import ReasLib.RingTheory.RingHom.IndEtale.Colimit
public import ReasLib.RingTheory.Smooth.Normal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Normality and ind-etale maps

Normality ascends along ind-etale ring maps.  The categorical filtered-colimit
presentation remains behind this ring-map interface.

@stack 06DI
-/

@[expose] public section

universe u v

namespace RingHom.IndEtale

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Normality ascends along an ind-etale algebra map. -/
@[stacks 06DI "normality ascends along ind-etale maps"]
theorem isNormalRing (h : (algebraMap R S).IndEtale) [IsNormalRing R] :
    IsNormalRing S := sorry

end RingHom.IndEtale
