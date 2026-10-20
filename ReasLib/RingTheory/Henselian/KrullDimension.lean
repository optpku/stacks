/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

namespace HenselianLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Stacks Lemma 10.153.10 (tag `06RS`): a zero-dimensional local ring is
henselian.  The Krull-dimension bound is an explicit owner input rather than a
global instance, so downstream users can apply this criterion without adding a
search-polluting Henselian instance.

@stack 06RS -/
@[stacks 06RS "zero-dimensional local rings are henselian"]
theorem of_krullDimLE_zero [Ring.KrullDimLE 0 R] :
    HenselianLocalRing R := sorry

end HenselianLocalRing
