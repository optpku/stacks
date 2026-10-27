/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Substack.LocallyClosed

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- The restricted groupoid fibration of a locally closed substack. -/
def category (U : Substack.LocallyClosed X) : GroupoidsOver S :=
  Substack.category X U.val U.property.2.choose

/-- The literal inclusion of a locally closed substack into its ambient stack. -/
def inclusion (U : Substack.LocallyClosed X) : category U ⟶ X :=
  Substack.inclusion X U.val U.property.2.choose

/-- The restricted groupoid fibration of a locally closed substack is an algebraic stack. -/
instance instAlgebraicStack_category (U : Substack.LocallyClosed X) :
    AlgebraicStack (category U) :=
  U.property.2.choose_spec.1

/-- The literal inclusion of a locally closed substack is an immersion. -/
instance instImmersion_inclusion (U : Substack.LocallyClosed X) :
    Groupoids.Hom.Immersion (inclusion U) :=
  U.property.2.choose_spec.2

variable [AlgebraicStack X]

/-- The underlying point-set of a locally closed substack is the image of its inclusion. -/
def pointsSet (U : Substack.LocallyClosed X) : Set (Points X) :=
  Set.range (Points.map (inclusion U))

/-- The point-set of a locally closed substack is the range of the induced map on points. -/
theorem pointsSet_eq (U : Substack.LocallyClosed X) :
    U.pointsSet = Set.range (Points.map (inclusion U)) := sorry

/-- A point belongs to a locally closed substack exactly when it is the image of a point
of the restricted stack. -/
theorem mem_pointsSet (U : Substack.LocallyClosed X) {x : Points X} :
    x ∈ U.pointsSet ↔ ∃ y : Points (category U), Points.map (inclusion U) y = x := sorry

end AlgebraicGeometry.AlgebraicStack.Substack.LocallyClosed
