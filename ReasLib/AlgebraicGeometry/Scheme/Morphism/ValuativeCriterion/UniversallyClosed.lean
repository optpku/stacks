/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Universal closedness and the valuative criterion

This leaf exposes the existence consequence of the valuative criterion as a directly reusable
theorem. The full characterization remains owned by mathlib.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A universally closed morphism satisfies the existence part of the valuative criterion. -/
@[stacks 01KF "universally closed implies valuative existence"]
theorem UniversallyClosed.valuativeCriterion
    (f : X ⟶ Y) [UniversallyClosed f] :
    ValuativeCriterion.Existence f := sorry

end AlgebraicGeometry
