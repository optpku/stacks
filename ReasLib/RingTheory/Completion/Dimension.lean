/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReasLib.RingTheory.Completion.FaithfullyFlat
public import ReasLib.RingTheory.KrullDimension.GoingDown
import Mathlib.Tactic.CrossRefAttribute

/-!
# Krull Dimension of a Maximal-Ideal Completion

@stack 07NV
-/

@[expose] public section

open IsLocalRing

universe u

namespace AdicCompletion

/-- A Noetherian local ring and its maximal-ideal adic completion have the same
Krull dimension. -/
@[stacks 07NV "Krull dimension and maximal-ideal completion"]
theorem ringKrullDim_eq (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    ringKrullDim A = ringKrullDim (AdicCompletion (maximalIdeal A) A) := sorry

end AdicCompletion
