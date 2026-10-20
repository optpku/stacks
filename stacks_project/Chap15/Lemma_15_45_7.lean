/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Henselian.Henselization.KrullDimension

@[expose] public section

/-!
# Lemma 15.45.7 (06LK)

@stack 06LK
-/

-- Lemma 15.45.7 (1): a local ring and a henselization have the same
-- Krull dimension.
@[stacks 06LK "Lemma 15.45.7 (1)"]
#check @IsHenselizationOf.ringKrullDim_eq

-- Lemma 15.45.7 (2): a local ring and a strict henselization have the
-- same Krull dimension.
@[stacks 06LK "Lemma 15.45.7 (2)"]
#check @IsStrictHenselizationOf.ringKrullDim_eq
