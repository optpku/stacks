/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.Completion.Nagata

@[expose] public section

/-!
# Complete Regular Local Rings

For a complete regular local domain, use `IsCompleteLocalRing.isN2Ring_of_domain`.
Its Noetherian hypothesis follows from `IsRegularLocalRing`.
-/
