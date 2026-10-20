/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Lower-Universe Initial Segments of Cardinals

This module packages the cardinals in one universe whose lifts are bounded by a cardinal in
another universe.  The direct subtype avoids exposing a chosen supremum or shrink model to
downstream users.
-/

universe w z

namespace Cardinal

/-- The lower-universe cardinals whose lifts are bounded by `kappa`. -/
@[stacks 079E "lower cardinal initial segment"]
def LowerInitialSegment (kappa : Cardinal.{z}) :=
  { c : Cardinal.{w} // Cardinal.lift.{z} c ≤ Cardinal.lift.{w} kappa }

namespace LowerInitialSegment

/-- Membership in a lower cardinal initial segment supplies the defining lifted inequality. -/
theorem lift_le {kappa : Cardinal.{z}} (c : LowerInitialSegment.{w, z} kappa) :
    Cardinal.lift.{z} c.1 ≤ Cardinal.lift.{w} kappa := sorry

/-- A lower cardinal initial segment is small in its lower universe when the upper bound has a
small model there. -/
instance small (kappa : Cardinal.{z}) [Small.{w} kappa.out] :
    Small.{w} (LowerInitialSegment.{w, z} kappa) := sorry

end LowerInitialSegment

end Cardinal
