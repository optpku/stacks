/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Kummer.FiniteLevel.EliminateRamification
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.116.16

The exact-level descent statement is recalled from the reusable finite-level descent owner.

@stack 09F5
-/

open KummerArtinSchreier
open KummerArtinSchreier.FiniteLevel
open IsLocalRing

/-! Lemma 15.116.16: finite-level descent. -/
@[stacks 09F5 "Lemma 15.116.16: finite-level descent"]
#check @KummerArtinSchreier.FiniteLevel.Descent.exists_totallyRamified

/-! The explicit composite-extension view is available when the tower instance is already installed. -/
#check @KummerArtinSchreier.FiniteLevel.Descent.exists_totallyRamified_of_extension

/-! The residue-field side condition uses the shared stable positive-power intersection. -/
#check @PerfectClosure.powerIntersection
#check @PerfectClosure.mem_powerIntersection_iff
#check @KummerArtinSchreier.FiniteLevel.IsAtLevel.OnBaseChange
#check @KummerArtinSchreier.FiniteLevel.IsAtLevel.OnBaseChange.toAfterBaseChange
