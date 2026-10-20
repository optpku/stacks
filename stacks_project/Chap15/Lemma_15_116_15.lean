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
# Lemma 15.116.15

The source alternative is recalled from the reusable finite-level base-change owner.

@stack 09F4
-/

open KummerArtinSchreier
open KummerArtinSchreier.FiniteLevel

/-! Lemma 15.116.15: finite-level base change alternative. -/
@[stacks 09F4 "Lemma 15.116.15: finite-level base change alternative"]
#check @KummerArtinSchreier.FiniteLevel.BaseChange.exists_totallyRamified

/-! The explicit composite-extension view avoids a statement-level tower pin for downstream use. -/
#check @KummerArtinSchreier.FiniteLevel.BaseChange.exists_totallyRamified_of_extension

/-! The recalled statement is expressed through the shared finite-level support and branch views. -/
#check @KummerArtinSchreier.FiniteLevel.IsExtension.OnBaseChange
#check @KummerArtinSchreier.FiniteLevel.IsExtension.OnBaseChange.toAfterBaseChange
#check @DVR.Field.IsTotallyRamified
#check @IsWeakSolutionFor
