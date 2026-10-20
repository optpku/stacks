/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.Defs
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.9.4

@stack 00CQ
-/

universe u

section

variable {A : Type u} [CommRing A] (S : Submonoid A)

/- Lemma 10.9.4: the localization `S⁻¹A` is the zero ring if and only if
`0 ∈ S`. -/
@[stacks 00CQ]
#check (IsLocalization.subsingleton_iff :
  Subsingleton (Localization S) ↔ (0 : A) ∈ S)

end
