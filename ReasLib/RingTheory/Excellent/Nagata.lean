/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Excellent
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Quasi-Excellent Rings Are Nagata

The mathematical theorem is universe-polymorphic. The canonical instance is restricted to the
same-universe owner so that its universe parameter is determined by the instance head.

@stack 07QV
-/

universe u v

namespace IsQuasiExcellentRing

/-- Lemma 15.52.5 (Tag 07QV): every quasi-excellent ring is Nagata. -/
@[stacks 07QV]
theorem nagataRing
    (R : Type u) [CommRing R] [IsQuasiExcellentRing.{u, v} R] : NagataRing R := sorry

/-- Quasi-excellence in the ring's universe canonically supplies the Nagata instance. -/
@[stacks 07QV "same-universe Nagata instance"]
instance toNagataRing
    (R : Type u) [CommRing R] [IsQuasiExcellentRing.{u, u} R] : NagataRing R := sorry

end IsQuasiExcellentRing

section

variable (R : Type u) [CommRing R] [IsQuasiExcellentRing.{u, u} R]

#synth NagataRing R

end
