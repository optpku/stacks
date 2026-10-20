/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.InheritedPrecoverage.Basic
public import ReasLib.CategoryTheory.Sites.Precoverage.Continuous
public import ReasLib.CategoryTheory.Sites.Precoverage.CoverLifting
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cartesian functors and inherited precoverages

A cartesian functor over a common base carries strongly-cartesian lifts of a precoverage to
strongly-cartesian lifts of the same precoverage.  It also preserves the pullbacks that occur
along those covering arrows.  This is the coverwise owner used before passing to generated
Grothendieck topologies.
-/

@[expose] public section

universe uC vC uS₁ vS₁ uS₂ vS₂

namespace CategoryTheory

namespace Precoverage.StronglyCartesianLift

variable {C : Type uC} [Category.{vC} C]
variable {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

/-- A cartesian functor maps the strongly-cartesian lift of any precoverage into the
corresponding lift on its target. -/
@[stacks 06NW "cartesian functors preserve inherited covering families"]
theorem le_comap
    (P : Precoverage C) (F : CartesianBasedFunctor p₁ p₂) :
    P.stronglyCartesianLift p₁ ≤
      (P.stronglyCartesianLift p₂).comap F.toFunctor := sorry

/-- A cartesian functor preserves inherited covering families and the pullbacks that occur along
their arrows.  The pullback hypothesis concerns only covering families in `P`. -/
@[stacks 06NW "coverwise continuity of cartesian functors"]
instance isContinuous
    (P : Precoverage C) (F : CartesianBasedFunctor p₁ p₂)
    [p₁.IsFibered] :
    Functor.Precoverage.IsContinuous F.toFunctor
      (P.stronglyCartesianLift p₁) (P.stronglyCartesianLift p₂) := sorry

/-- A cartesian functor admits selected-cover lifts between the strongly-cartesian
precoverages.  This is the coverwise owner of cocontinuity for inherited topologies. -/
@[stacks 06NW "cover lifting for inherited precoverages"]
instance hasCoverLifts
    (P : Precoverage C) (F : CartesianBasedFunctor p₁ p₂)
    [P.HasPullbacks] [p₁.IsFibered] :
    Functor.Precoverage.HasCoverLifts F.toFunctor
      (P.stronglyCartesianLift p₁) (P.stronglyCartesianLift p₂) := sorry

end Precoverage.StronglyCartesianLift

end CategoryTheory
