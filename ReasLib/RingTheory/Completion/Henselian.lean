/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Henselian
public import ReasLib.RingTheory.Completion.LocalRing
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Henselian complete local rings

This leaf specializes Mathlib's adic-completeness henselian instance to the
project's `IsCompleteLocalRing` owner.  The specialization is kept in
`IsCompleteLocalRing` so downstream code gets the canonical local instance by
typeclass search without rebuilding the maximal-ideal argument.
-/

universe u

namespace IsCompleteLocalRing

variable {R : Type u} [CommRing R] [IsCompleteLocalRing R]

/-- A complete local ring is henselian for its canonical local-ring structure.

This is the `maximalIdeal` specialization of Mathlib's
`IsAdicComplete.henselianRing` instance. -/
@[stacks 04GM "complete local rings are henselian"]
instance henselianLocalRing : HenselianLocalRing R := sorry

end IsCompleteLocalRing
