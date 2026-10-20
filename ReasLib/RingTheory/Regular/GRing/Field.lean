/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Regular.GRing

/-!
# Fields are G-rings

@stack 07PX
-/

@[expose] public section

universe u

namespace IsGRing

/-- Every field is a G-ring. -/
@[stacks 07PX "fields are G-rings"]
instance field (K : Type u) [Field K] : IsGRing K := sorry

end IsGRing
