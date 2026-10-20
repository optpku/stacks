/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.Syntomic.LocalCompleteIntersection

/-!
# Lemma 15.33.5

@stack 07D3
-/

@[expose] public section

/-!
# Syntomic and Local Complete Intersection Recall

The intrinsic ring-hom equivalence belongs in ReasLib.  The textbook wording is
recovered directly from `RingHom.Syntomic.iff_flat_and_isLocalCompleteIntersection`.
-/

/- Lemma 15.33.5, tag `07D3`: a ring map is syntomic
if and only if it is flat and a local complete intersection. -/
@[stacks 07D3 "syntomic ring maps"]
#check RingHom.Syntomic.iff_flat_and_isLocalCompleteIntersection

#check @RingHom.Syntomic.iff_flat_and_isLocalCompleteIntersection
