/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Catenary.Formal.ToUniversal

@[expose] public section

/-!
# Lemma 15.110.4

@stack 0AW5
-/

universe u v

/- Lemma 15.110.4 (current Stacks numbering: Lemma 15.111.4, tag `0AW5`):
a formally catenary Noetherian local ring is universally catenary. -/
@[stacks 0AW5 "Lemma 15.110.4"]
#check fun (A : Type u) [CommRing A] [IsFormallyCatenaryRing A] ↦
  (inferInstance : UniversallyCatenaryRing.{u, v} A)
