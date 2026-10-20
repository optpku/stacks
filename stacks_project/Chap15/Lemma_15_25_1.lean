/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.PrimeLocalization
import StacksCheckRecall

/-!
# Lemma 15.25.1

@stack 053A

The prime-local finite-presentation criterion for flat polynomial modules is owned by the
reusable finite-presentation API.
-/

@[expose] public section

/- The finite prime-localization detection condition used in Lemma 15.25.1. -/
#check @PrimeLocalization.DetectsEquality

/- Lemma 15.25.1: a finite flat module over a finite-variable polynomial ring is finitely
presented when all prime-local base changes are finitely presented and finitely many base-prime
localizations detect equality. -/
@[stacks 053A "Lemma 15.25.1"]
#check @Module.FinitePresentation.ofFlatPrimeLocalizations
