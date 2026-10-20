/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Kaehler
public import ReasLib.RingTheory.Kaehler.Unramified
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.131.8

@stack 00RT
-/

/- Lemma 10.131.8 (1) [stacks 00RT]: canonical recall of source-localization
invariance of the Kähler-differential comparison map. -/

@[stacks 00RT]
#check @KaehlerDifferential.map_bijective_of_isLocalization_source

/- Lemma 10.131.8 (2) [stacks 00RT]: canonical recall of the localization
description of `Ω`. -/

@[stacks 00RT]
#check @KaehlerDifferential.isLocalizedModule_map
