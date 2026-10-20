/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints

/-!
# Embedded associated points of scheme modules

This leaf builds the embedded-point predicate for a module from its associated
points and specialization.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open Set TopologicalSpace

variable {X : Scheme.{u}} (F : X.Modules)

/-- A point `x` is embedded associated for `F` when it is an associated point and is a
specialization of a distinct associated point. -/
def embeddedAssociatedAt (x : X) : Prop :=
  x ∈ associatedPoints F ∧
    ∃ y : X, y ∈ associatedPoints F ∧ y ≠ x ∧ y ⤳ x

/-- An embedded-associated point is an associated point. -/
theorem embeddedAssociatedAt.mem_associatedPoints {x : X}
    (hx : F.embeddedAssociatedAt x) :
    x ∈ associatedPoints F := sorry

/-- An embedded-associated point specializes from a distinct associated
point. -/
theorem embeddedAssociatedAt.exists_specializing_associated {x : X}
    (hx : F.embeddedAssociatedAt x) :
    ∃ y : X, y ∈ associatedPoints F ∧ y ≠ x ∧ y ⤳ x := sorry

/-- Unfold `embeddedAssociatedAt` into the associated-point and
specialization conditions. -/
theorem embeddedAssociatedAt_iff (x : X) :
    F.embeddedAssociatedAt x ↔
      x ∈ associatedPoints F ∧
        ∃ y : X, y ∈ associatedPoints F ∧ y ≠ x ∧ y ⤳ x := sorry

/-- The set of embedded associated points of `F`. -/
def embeddedAssociatedPoints : Set X :=
  F.embeddedAssociatedAt

/-- Membership in `embeddedAssociatedPoints` is the embedded-associated-point
predicate. -/
theorem mem_embeddedAssociatedPoints_iff (x : X) :
    x ∈ F.embeddedAssociatedPoints ↔ F.embeddedAssociatedAt x := sorry

/-- A module has no embedded associated points exactly when no point is
embedded associated. -/
theorem embeddedAssociatedPoints_eq_empty_iff :
    F.embeddedAssociatedPoints = (∅ : Set X) ↔
      ∀ x : X, ¬ F.embeddedAssociatedAt x := sorry

end AlgebraicGeometry.Scheme.Modules
