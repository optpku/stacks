/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Field
public import ReasLib.RingTheory.Excellent
public import ReasLib.RingTheory.Regular.GRing.Field
public import ReasLib.RingTheory.Regular.JRing.Field

@[expose] public section

/-!
# Excellent Fields

@stack 07QW
-/

universe u v

namespace IsExcellentRing

/-- Every field is excellent. -/
@[stacks 07QW "fields are excellent"]
instance field (K : Type u) [Field K] : IsExcellentRing.{u, v} K := sorry

end IsExcellentRing
