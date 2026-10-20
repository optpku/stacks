module

public import ReasLib.CategoryTheory.Fibered.InheritedPrecoverage.Basic
public import ReasLib.CategoryTheory.Sites.Precoverage.Continuous
public import ReasLib.CategoryTheory.Sites.Precoverage.CoverLifting
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection from an inherited precoverage

The projection of a fibred category sends its strongly-cartesian selected covers to the
original covers and admits selected-cover lifts in the opposite direction.  This file is the
precoverage-first owner; no groupoid condition or generated topology is needed.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory.Precoverage.StronglyCartesianLift.Projection

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

/-- Projecting a strongly-cartesian covering family gives a covering family in the base. -/
@[stacks 0CN0 "projection of strongly-cartesian covering families"]
theorem le_comap (P : Precoverage C) (p : S ⥤ C) :
    P.stronglyCartesianLift p ≤ P.comap p := sorry

/-- A fibred projection preserves strongly-cartesian selected covers and the pullbacks occurring
along their arrows. -/
@[stacks 0CN0 "continuity of an inherited-precoverage projection"]
instance isPrecoverageContinuous
    (P : Precoverage C) (p : S ⥤ C) [p.IsFibered] :
    Functor.Precoverage.IsContinuous p (P.stronglyCartesianLift p) P := sorry

/-- A fibred projection admits selected lifts of base covers to its strongly-cartesian lift
precoverage.  Only pullbacks of selected base covers are required. -/
@[stacks 0CN0 "cover lifting for an inherited-precoverage projection"]
instance hasCoverLifts
    (P : Precoverage C) (p : S ⥤ C) [P.HasPullbacks] [p.IsFibered] :
    Functor.Precoverage.HasCoverLifts p (P.stronglyCartesianLift p) P := sorry

end CategoryTheory.Precoverage.StronglyCartesianLift.Projection
