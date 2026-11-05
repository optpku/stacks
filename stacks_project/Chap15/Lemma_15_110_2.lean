/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Catenary.Formal.Universal

/-!
@stack 0AW3
-/

@[expose] public section

universe u v

/- Lemma 15.110.2 (current Stacks numbering: Lemma 15.111.2, tag `0AW3`):
if a Noetherian local ring is not formally catenary, then it is not universally
catenary. -/
@[stacks 0AW3 "Lemma 15.110.2"]
#check fun (A : Type u) [CommRing A] [IsLocalRing A]
    (hA : ¬ IsFormallyCatenaryRing A) ↦
  (IsFormallyCatenaryRing.not_universally.{u, v} (A := A) hA :
    ¬ UniversallyCatenaryRing.{u, max u v} A)
