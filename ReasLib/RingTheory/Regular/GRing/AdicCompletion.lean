/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Regular.GRing

@[expose] public section

/-!
# Adic Completions of G-Rings

@stack 07PW

Adic completion does not preserve the G-ring property without additional hypotheses.
-/

universe u

namespace IsGRing.AdicCompletion

/-- Remark 15.50.11 (Stacks 07PW): there is a G-ring with an adic completion that is not a
G-ring. -/
@[stacks 07PW]
theorem exists_not_isGRing :
    ∃ (R : Type u) (_ : CommRing R) (I : Ideal R),
      IsGRing R ∧ ¬ IsGRing (AdicCompletion I R) := sorry

end IsGRing.AdicCompletion
