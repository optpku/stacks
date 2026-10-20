/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation

/-!
# Finite presentation of scheme modules at a point

This file records finite presentation on an open neighbourhood of a point and
its relation to global finite presentation.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A scheme module is finitely presented at a point when its restriction to some open
neighbourhood of that point is finitely presented. -/
def IsFinitePresentationAt {X : Scheme.{u}} (F : X.Modules) (x : X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ (F.restrict U.ι).IsFinitePresentation

/-- Finite presentation at a point is equivalent to finite presentation on an open
neighbourhood containing that point. -/
theorem isFinitePresentationAt_iff {X : Scheme.{u}} (F : X.Modules) (x : X) :
    IsFinitePresentationAt F x ↔
      ∃ U : X.Opens, x ∈ U ∧ (F.restrict U.ι).IsFinitePresentation := sorry

namespace IsFinitePresentation

/-- A globally finitely presented scheme module is finitely presented at every point. -/
theorem isFinitePresentationAt {X : Scheme.{u}} (F : X.Modules)
    [F.IsFinitePresentation] (x : X) :
    Scheme.Modules.IsFinitePresentationAt F x := sorry

end IsFinitePresentation

end AlgebraicGeometry.Scheme.Modules
