/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Catenary.Formal.Ratliff

/-!
@stack 0AW6
-/

@[expose] public section

universe u v

/- Proposition 15.110.5 (current Stacks numbering: Proposition 15.111.5,
Ratliff, tag `0AW6`): a Noetherian local ring is universally catenary if and
only if it is formally catenary. -/
@[stacks 0AW6 "Proposition 15.110.5 (Ratliff)"]
#check fun (A : Type u) [CommRing A] [IsLocalRing A] ↦
  (UniversallyCatenaryRing.iff_formallyCatenary (A := A) :
    UniversallyCatenaryRing.{u, v} A ↔ IsFormallyCatenaryRing A)
