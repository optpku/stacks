/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed.Localization
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed.Quotient

@[expose] public section

/- Lemma 15.14.3 (1): quotients of absolutely integrally closed rings are
absolutely integrally closed. -/
/-!
@stack 0DCN
-/
@[stacks 0DCN "Lemma 15.14.3 (1): quotients"]
#check @IsAbsolutelyIntegrallyClosed.quotient

/- Lemma 15.14.3 (2): arbitrary localization models of absolutely integrally
closed rings are absolutely integrally closed. -/
@[stacks 0DCN "Lemma 15.14.3 (2): localizations"]
#check @IsAbsolutelyIntegrallyClosed.of_isLocalization

/- The canonical localization instance is available to typeclass search. -/
#check @IsAbsolutelyIntegrallyClosed.localization
